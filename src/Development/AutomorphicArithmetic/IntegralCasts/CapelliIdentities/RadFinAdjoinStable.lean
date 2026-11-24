module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Basic.Complex.Basic
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

noncomputable def UpperTheory.Reformulated.B.Qj9.Stable :
    {M : Type} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → Set (Module.End ℂ M) → Submodule ℂ M → Prop :=
    fun {M : Type} [AddCommGroup M] [_root_.Module ℂ M] (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) ↦
      ∀ g ∈ Op, ∀ x ∈ P, (g : M → M) x ∈ P

theorem UpperTheory.Reformulated.B.Qj9.radFin_adjoin_stable :
    ∀ {M : Type} [inst : AddCommGroup M] [inst_1 : _root_.Module ℂ M] (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M),
      UpperTheory.Reformulated.B.Qj9.Stable Op P → ∀ e ∈ Algebra.adjoin ℂ Op, ∀ x ∈ P, (e : M → M) x ∈ P := by
  intro M _ _ Op P h e he
  induction he using Algebra.adjoin_induction with
  | mem g hg => exact h g hg
  | algebraMap r =>
    intro x hx
    rw [Module.algebraMap_end_apply]
    exact P.smul_mem r hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.add_apply]
    exact P.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [Module.End.mul_apply]
    exact ha _ (hb x hx)
