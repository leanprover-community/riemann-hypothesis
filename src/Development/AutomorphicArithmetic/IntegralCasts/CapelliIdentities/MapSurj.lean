module

public import Mathlib.RingTheory.TensorProduct.Maps
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

theorem UpperTheory.Reformulated.B.Qk2.map_surj :
    ∀ {A E : Type} [inst : CommRing A] [inst_1 : Ring E]
    [inst_2 : Algebra A E] {E' : Type} [inst_3 : Ring E'] [inst_4 : Algebra A E'] (f : E' →ₐ[A] E),
    Function.Surjective (⇑f : E' → E) →
      ∀ (S : Type) [inst_5 : CommRing S] [inst_6 : Algebra A S],
        Function.Surjective
          (⇑(Algebra.TensorProduct.map (AlgHom.id S S) f) : TensorProduct A S E' → TensorProduct A S E) := by
  intro A E _ _ _ E' _ _ f hf S _ _ x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s e =>
    obtain ⟨e', rfl⟩ := hf e
    exact ⟨TensorProduct.tmul A s e', by simp⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩
