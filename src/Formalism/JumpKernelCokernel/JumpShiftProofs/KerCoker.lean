module

public import Formalism.JumpKernelCokernel.Statement
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
import Mathlib.Order.CompletePartialOrder
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

namespace Formalism.KernelCokernelLengths.KernelCokernelLemmas

theorem main (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (f : Module.End O M) (N : Submodule O M) (hN : N.map f ≤ N) :
    Module.length O (↥N ⧸ (N.map f).comap N.subtype) ≤ Module.length O (LinearMap.ker f) := by
  have hNf : ∀ x ∈ N, f x ∈ N := fun x hx => hN (Submodule.mem_map_of_mem hx)
  let g : N →ₗ[O] ↥((N.map f).comap N.subtype) :=
    LinearMap.codRestrict ((N.map f).comap N.subtype) (f.restrict hNf)
      (fun x => Submodule.mem_comap.2 (Submodule.mem_map_of_mem x.2))
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_comap.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hxy)⟩
  have hNfin : Module.length O N ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective N.subtype N.injective_subtype)
  have hQfin : Module.length O ((N.map f).comap N.subtype) ≠ ⊤ :=
    ne_top_of_le_ne_top hNfin (Module.length_le_of_injective _ (Submodule.injective_subtype _))
  have e1 := Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype ((N.map f).comap N.subtype))
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ ((N.map f).comap N.subtype))
  have e2 := Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype (LinearMap.ker g)) hgs
    (LinearMap.exact_subtype_ker_map g)
  have e3 : Module.length O (↥N ⧸ (N.map f).comap N.subtype) = Module.length O (LinearMap.ker g) := by
    rw [e1, add_comm] at e2
    exact WithTop.add_right_cancel hQfin e2
  rw [e3]
  refine Module.length_le_of_injective
    (LinearMap.codRestrict (LinearMap.ker f) (N.subtype.comp (LinearMap.ker g).subtype) ?_) ?_
  · intro x
    exact LinearMap.mem_ker.2
      (congrArg (fun z : ↥((N.map f).comap N.subtype) => ((z : N) : M)) (LinearMap.mem_ker.1 x.2))
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    exact h

end Formalism.KernelCokernelLengths.KernelCokernelLemmas
