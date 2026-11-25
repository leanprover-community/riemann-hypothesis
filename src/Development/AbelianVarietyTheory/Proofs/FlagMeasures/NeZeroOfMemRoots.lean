module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors

@[expose] public section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys.LabLoc

open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem eq_of_roots_eq {f h : (ZMod g)[X]} (hf : f.Monic) (hh : h.Monic)
    (e : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar h) : f = h := by
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
  rw [(IsAlgClosed.splits (f.map _)).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (h.map _)).eq_prod_roots_of_monic (hh.map _)]
  exact congrArg (fun m : Multiset (Formalism.CyclotomicNorms.Fbar g) => (m.map fun a => X - C a).prod) e

theorem ne_zero_of_mem_roots {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : x ∈ Formalism.CyclotomicNorms.rootsBar f) : x ≠ 0 := by
  rintro rfl
  have hf : f.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) ≠ 0 := (mem_roots'.1 hx).1
  have := (mem_roots'.1 hx).2
  rw [IsRoot, eval_map, eval₂_at_zero] at this
  exact h0 ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (by simpa using this))

theorem map_eq_map {τ : Formalism.CyclotomicNorms.Fbar g →* ℂ} (hτ : Set.InjOn τ {x | x ≠ 0}) {A B : Multiset (Formalism.CyclotomicNorms.Fbar g)}
    (hA : ∀ x ∈ A, x ≠ 0) (hB : ∀ x ∈ B, x ≠ 0) (e : A.map τ = B.map τ) : A = B := by
  rw [Multiset.ext]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [Multiset.count_eq_zero.2 (fun h => hA 0 h rfl), Multiset.count_eq_zero.2 (fun h => hB 0 h rfl)]
  have key : ∀ C : Multiset (Formalism.CyclotomicNorms.Fbar g), (∀ y ∈ C, y ≠ 0) → C.count x = (C.map τ).count (τ x) := by
    intro C hC
    rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
    congr 1
    refine Multiset.filter_congr fun y hy => ⟨fun h => h ▸ rfl, fun h => hτ hx (hC y hy) h⟩
  rw [key A hA, key B hB, e]

theorem actK_finset_sum {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) ℚ_[g]) V) {ι : Type} (T : Finset ι) (a : ι → MonoidAlgebra ℂ (Gn g n)) :
    actK ρ (∑ i ∈ T, a i) = ∑ i ∈ T, actK ρ (a i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [actK]
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp [actK, add_smul, Finset.sum_add_distrib]

theorem actK_one_of_mem {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 ρ) : actK ρ 1 v = v := by
  have hs : actK ρ 1 = ρ (lift g n 1) := by
    unfold actK
    rw [MonoidAlgebra.one_def, Finset.sum_eq_single 1]
    · simp
    · intro y _ hy
      simp [Finsupp.single_eq_of_ne hy]
    · simp
  have hk : red g n (Function.invFun (red g n) 1) = 1 := Function.invFun_eq ⟨1, map_one _⟩
  rw [hs, lift]
  have := (Submodule.mem_iInf _).1 hv ⟨_, hk⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  simpa using this

end GlobalTheory.SerSys.LabLoc
