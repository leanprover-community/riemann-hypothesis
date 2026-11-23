module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem map_range_mul_of_periodic {β : Type} (g : ℕ → β) (e : ℕ) (hg : ∀ i, g (e + i) = g i) (m : ℕ) :
    (Multiset.range (e * m)).map g = m • (Multiset.range e).map g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, add_comm (e * m), Multiset.range_add, Multiset.map_add (f := _), Multiset.map_map,
      succ_nsmul', ← ih]
    congr 1
    exact Multiset.map_congr rfl fun i _ => hg i

theorem roots_pow_eq_map_range {F : Type} [Field F] [Finite F] (f : F[X]) (m : ℕ) (hf : f.Monic)
    (hi : Irreducible f) (α : AlgebraicClosure F)
    (hα : α ∈ ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots) :
    ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots =
      (Multiset.range (f ^ m).natDegree).map fun i => α ^ Nat.card F ^ i := by
  rw [Polynomial.map_pow, roots_pow] at hα ⊢
  have h1 := Multiset.mem_of_mem_nsmul hα
  have h2 : aeval α f = 0 := by
    rw [← eval_map_algebraMap]
    exact (mem_roots'.1 h1).2
  have h3 : f = minpoly F α := minpoly.eq_of_irreducible_of_monic hi h2 hf
  have hper := (minpoly_natDegree_dvd_iff_pow α _).1 dvd_rfl
  rw [natDegree_pow, mul_comm, h3, roots_minpoly_eq_map_range, map_range_mul_of_periodic]
  intro i
  simp only [pow_add, pow_mul, hper]

theorem natDegree_mul_esymm_roots_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X]) (m k s : ℕ), f.Monic → Irreducible f → ((f ^ m).natDegree : ℂ) * (((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s = ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s, rootSum θ (k * ∑ i ∈ I, Nat.card F ^ i) (f ^ m) := by
  intro F _ _ θ f m k s hf hi
  set R := ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots with hR
  have hcard : R.card = (f ^ m).natDegree := by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]
  have key : ∀ α ∈ R, (R.map fun α => θ α ^ k).esymm s =
      ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s,
        θ α ^ (k * ∑ i ∈ I, Nat.card F ^ i) := by
    intro α hα
    have h := roots_pow_eq_map_range f m hf hi α hα
    rw [← hR] at h
    conv_lhs => rw [h]
    rw [Multiset.map_map, ← Finset.range_val, Finset.esymm_map_val]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp, map_pow, ← pow_mul, mul_comm]
  have h2 : (R.map fun _ => (R.map fun α => θ α ^ k).esymm s).sum =
      (R.map fun α => ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s,
        θ α ^ (k * ∑ i ∈ I, Nat.card F ^ i)).sum := by
    rw [Multiset.map_congr rfl key]
  rw [Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul] at h2
  rw [h2, Multiset.sum_map_sum]
  rfl

end GlobalTheory.CuspGL
