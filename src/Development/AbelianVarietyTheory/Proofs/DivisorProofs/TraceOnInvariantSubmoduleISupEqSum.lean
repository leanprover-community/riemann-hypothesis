module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Mathlib.Algebra.DirectSum.LinearMap
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_iSup_eq_sum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (M : ι → Submodule ℂ V)
    (L : V →ₗ[ℂ] V), iSupIndep M → (∀ i, FiniteDimensional ℂ (M i)) → (∀ i, ∀ v ∈ M i, L v ∈ M i) →
    trOn (⨆ i, M i) L = ∑ i, trOn (M i) L := by
  intro V _ _ ι _ M L hind hfin hinv
  haveI := hfin
  have hp : (⨆ i, M i) = ⨆ i ∈ (Finset.univ : Finset ι), M i := by simp
  have hs : iSupIndep (fun i : (Finset.univ : Finset ι) ↦ M i) :=
    hind.comp Subtype.val_injective
  have hf : ∀ i, Set.MapsTo L (M i) (M i) := fun i v hv ↦ hinv i v hv
  have hsup : ∀ v ∈ (⨆ i, M i), L v ∈ (⨆ i, M i) := by
    intro v hv
    refine Submodule.iSup_induction M (motive := fun v ↦ L v ∈ ⨆ i, M i) hv ?_ ?_ ?_
    · intro i x hx; exact Submodule.mem_iSup_of_mem i (hinv i x hx)
    · simp
    · intro x y hx hy; rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup (N := M) Finset.univ hs hf
    (⨆ i, M i) hp hsup
  unfold trOn
  rw [dite_eq_left hsup, key]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dite_eq_left (hinv i)]

end GlobalTheory.BCT
