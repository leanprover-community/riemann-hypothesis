module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

theorem UpperTheory.finite_span_add_smul :
    ∀ {ι V : Type} [AddCommGroup V] [Module ℂ V] (T : ι → V →ₗ[ℂ] V) (S : Set ι) (a b : V) (z : ℂ),
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i a) '' S)) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i b) '' S)) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun i => T i (a + z • b)) '' S)) := by
  intro ι V _ _ T S a b z ha hb
  have hle : Submodule.span ℂ ((fun i => T i (a + z • b)) '' S) ≤
      Submodule.span ℂ ((fun i => T i a) '' S) ⊔ Submodule.span ℂ ((fun i => T i b) '' S) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [map_add (f := _), map_smul, SetLike.mem_coe]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨i, hi, rfl⟩)
      (Submodule.smul_mem _ z (Submodule.subset_span ⟨i, hi, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle
