module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace UpperTheory.Reformulated.B.Gr23

open Polynomial

private theorem eval_prod (m : Multiset ℂ) (u : ℂ) :
    ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod.eval u
      = (m.map (fun x : ℂ ↦ u + x)).prod := by
  rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun x _ ↦ ?_
  simp

private theorem eq_of_prod_eq {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (fun x : ℂ ↦ u + x)).prod = (m'.map (fun x : ℂ ↦ u + x)).prod) :
    m = m' := by
  have hp : ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod
      = ((m'.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod := by
    refine Polynomial.funext fun u ↦ ?_
    rw [eval_prod, eval_prod, h u]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

theorem abs {M : Type*} [AddCommGroup M] [Module ℂ M] {V : Submodule ℂ M} (hV : V ≠ ⊥)
    (T : ℂ → Module.End ℂ M) {a : ℕ} {m m' : Multiset ℂ}
    (h : m.card = a ∧ ∀ (u : ℂ), ∀ φ ∈ V,
      (T u) φ = (Multiset.map (fun (x : ℂ) ↦ u + x) m).prod • φ)
    (h' : m'.card = a ∧ ∀ (u : ℂ), ∀ φ ∈ V,
      (T u) φ = (Multiset.map (fun (x : ℂ) ↦ u + x) m').prod • φ) :
    m = m' := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  refine eq_of_prod_eq fun u ↦ ?_
  exact smul_left_injective ℂ hφ0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))

end UpperTheory.Reformulated.B.Gr23
