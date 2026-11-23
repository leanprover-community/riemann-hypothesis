module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusCharacterOrthogonality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenFunctionCharacterSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMinpolyPowEqSumStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem psiG_rootSum_pair_prod_rootSum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (m k l : ℕ) (e : Fin l → ℕ), 0 < m → ∑ᶠ x, psiG (rootSum θ k) m x * star (chG (fun P => ∏ j, rootSum θ (e j) P) m x) = (Nat.card (GL (Fin m) F) : ℂ) * ((Finset.univ.filter fun a : Fin l → Fin m => k ≡ ∑ j, e j * Nat.card F ^ (a j : ℕ) [MOD Nat.card F ^ m - 1]).card : ℂ) := by
  intro F _ _ θ hθ m k l e hm
  set q := Nat.card F with hq
  have hq1 : 1 < q := Finite.one_lt_card
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq1
  set N := q ^ m - 1 with hN
  have hN0 : 0 < N := by omega
  have hcast : ((q : ℂ) ^ m - 1) = ((N : ℕ) : ℂ) := by
    rw [hN, Nat.cast_sub hqm.le]; push_cast; ring
  have hNne : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have htor := GlobalTheory.T.green_function_character_sum F θ m k (fun P => ∏ j, rootSum θ (e j) P) hm
  have horth := (GlobalTheory.CuspGL.torus_orthogonality F θ hθ m hm).2
  set T := {α : AlgebraicClosure F | α ^ N = 1} with hT
  have hTfin : T.Finite := by
    apply (Polynomial.nthRoots N (1 : AlgebraicClosure F)).toFinset.finite_toSet.subset
    intro α hα
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots hN0).2 hα
  have key : ∀ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)))
      = ∑ a : Fin l → Fin m, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ))) := by
    intro α hα
    have hr : ∀ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)) = ∑ a : Fin m, θ α ^ (e j * q ^ (a : ℕ)) :=
      fun j => (GlobalTheory.T.rootSum_minpoly_pow_eq_sum_range F θ m (e j) α hm hα).trans (Finset.sum_range (fun a => θ α ^ (e j * q ^ a)))
    simp_rw [hr]
    rw [← Finset.mul_sum, ← star_sum, Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ᶠ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)))
      = ∑ a : Fin l → Fin m, ∑ᶠ α ∈ T, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ))) := by
    rw [finsum_mem_congr rfl key, finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ hTfin]
  rw [hsum] at htor
  simp_rw [horth] at htor
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hcast] at htor
  apply mul_left_cancel₀ hNne
  rw [htor]
  ring

end GlobalTheory.Shin
