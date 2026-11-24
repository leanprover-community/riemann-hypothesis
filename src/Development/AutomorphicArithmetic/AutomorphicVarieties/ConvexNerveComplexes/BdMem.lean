module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
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

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.bd_mem :
    ∀ {I : Type} {S : ∀ n, Set (Fin n → I)}, FaceClosed S → ∀ (n : ℕ) (c : Ch I (n + 1)), c ∈ Finsupp.supported ℤ ℤ (S (n + 1)) → bd I n c ∈ Finsupp.supported ℤ ℤ (S n) := by
  intro I S hS n c hc
  rw [bd, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
  exact Finsupp.single_mem_supported ℤ _ (hS n t (hc (Finset.mem_coe.2 ht)) j)
