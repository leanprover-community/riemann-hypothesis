module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
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
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.partStable :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
      {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
      (i : ι) (K : Submodule ℂ (M i)),
      (∀ g : Module.End ℂ M₀, ∀ t ∈ part (M₀ := M₀) i K,
        TensorProduct.map g LinearMap.id t ∈ part (M₀ := M₀) i K) ∧
      (∀ g : Module.End ℂ (M i), (∀ x ∈ K, g x ∈ K) → ∀ t ∈ part (M₀ := M₀) i K,
        factorOp i g t ∈ part (M₀ := M₀) i K) ∧
      ∀ l, l ≠ i → ∀ g : Module.End ℂ (M l), ∀ t ∈ part (M₀ := M₀) i K,
        factorOp l g t ∈ part (M₀ := M₀) i K := by
  intro ι _ _ M₀ _ _ M _ _ i K
  have mem : ∀ (r : M₀ × ∀ j, M j), ∀ x ∈ K,
      intersection_update_fsHerm_neg_one i r x ∈ part (M₀ := M₀) i K := fun r x hx =>
    (le_iSup (fun r : M₀ × ∀ j, M j => K.map (intersection_update_fsHerm_neg_one i r)) r) (Submodule.mem_map_of_mem hx)
  have key : ∀ Φ : Module.End ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)),
      (∀ (r : M₀ × ∀ j, M j), ∀ x ∈ K,
        Φ (intersection_update_fsHerm_neg_one i r x) ∈ part (M₀ := M₀) i K) →
      ∀ t ∈ part (M₀ := M₀) i K, Φ t ∈ part (M₀ := M₀) i K := by
    intro Φ h t ht
    have : part (M₀ := M₀) i K ≤ (part (M₀ := M₀) i K).comap Φ :=
      iSup_le fun r => Submodule.map_le_iff_le_comap.2 fun x hx => h r x hx
    exact this ht
  refine ⟨fun g => key _ fun r x hx => ?_, fun g hg => key _ fun r x hx => ?_,
    fun l hl g => key _ fun r x hx => ?_⟩
  · have := mem (g r.1, r.2) x hx
    simpa [position_apply] using this
  · have := mem r (g x) (hg x hx)
    rw [position_apply] at this
    rw [position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    convert this using 3
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  · have := mem (r.1, Function.update r.2 l (g (r.2 l))) x hx
    rw [position_apply] at this
    rw [position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    convert this using 3
    funext j
    by_cases hj : j = i
    · subst hj; simp [Function.update_of_ne hl.symm]
    · by_cases hj' : j = l
      · subst hj'; simp [Function.update_of_ne hj]
      · simp [Function.update_of_ne hj, Function.update_of_ne hj']
