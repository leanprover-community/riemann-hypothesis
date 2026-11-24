module

public import Formalism.GradedWeylDivisibility.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem mem_dualWeyl_iff {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔
      IsWeightedHomogeneous (colW r n) f ν ∧
        ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  unfold dualWeyl
  simp only [Submodule.mem_inf, mem_weightedHomogeneousSubmodule, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero]

theorem dualWeyl_mul {R : Type*} [CommRing R] {r n : ℕ} {ν μ : Fin n → ℕ}
    {f g : MvPolynomial (Fin r × Fin n) R}
    (hf : f ∈ dualWeyl R r n ν) (hg : g ∈ dualWeyl R r n μ) :
    f * g ∈ dualWeyl R r n (ν + μ) := by
  rw [mem_dualWeyl_iff] at *
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]

theorem one_mem_dualWeyl {R : Type*} [CommRing R] {r n : ℕ} :
    (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  rw [mem_dualWeyl_iff]
  refine ⟨isWeightedHomogeneous_one _ _, fun l j _ => ?_⟩
  rw [map_one, map_one]

theorem dualWeyl_pow {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (k : ℕ) :
    f ^ k ∈ dualWeyl R r n (k • ν) := by
  induction k with
  | zero => simpa using (one_mem_dualWeyl (R := R) (r := r) (n := n))
  | succ k ih => rw [pow_succ, succ_nsmul]; exact dualWeyl_mul ih hf

theorem dualWeyl_prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (ν : ι → Fin n → ℕ) (f : ι → MvPolynomial (Fin r × Fin n) R)
    (hf : ∀ i ∈ s, f i ∈ dualWeyl R r n (ν i)) :
    (∏ i ∈ s, f i) ∈ dualWeyl R r n (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one_mem_dualWeyl (R := R) (r := r) (n := n))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact dualWeyl_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem dualWeyl_of_eq {R : Type*} [CommRing R] {r n : ℕ} {ν μ : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (h : ν = μ) :
    f ∈ dualWeyl R r n μ := h ▸ hf

end Formalism.GradedWeylDivisibility
