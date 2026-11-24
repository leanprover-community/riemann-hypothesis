module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL


open Polynomial in
theorem _root_.GlobalTheory.CuspGL.ipGL_charpoly_eq_finsum_mass (F : Type) [Field F] [Finite F]
    (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V → ℂ) (s : F[X] → ℂ) :
    _root_.GlobalTheory.CuspGL.ipGL φ (fun g => s (LinearMap.charpoly g)) =
      ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0},
        _root_.GlobalTheory.CuspGL.mass φ P * star (s P) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective
  set S := {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0} with hS
  set I := S ∩ Set.range (fun g : Module.End F V => LinearMap.charpoly g) with hI
  have hunit : ∀ g : Module.End F V, IsUnit g ↔ LinearMap.charpoly g ∈ S := by
    intro g
    simp only [hS, Set.mem_setOf_eq, LinearMap.charpoly_monic, LinearMap.charpoly_natDegree,
      true_and]
    rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff, isUnit_iff_ne_zero]
    simp
  have hset : {g : Module.End F V | IsUnit g} =
      ⋃ P ∈ I, {g : Module.End F V | LinearMap.charpoly g = P} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, hI, Set.mem_inter_iff, Set.mem_range,
      exists_prop]
    rw [hunit]
    constructor
    · intro h
      exact ⟨_, ⟨h, g, rfl⟩, rfl⟩
    · rintro ⟨P, ⟨hP, _⟩, rfl⟩
      exact hP
  have hsupp : S ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P)) =
      I ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P)) := by
    ext P
    simp only [hI, Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hPS, hne⟩
      refine ⟨⟨hPS, ?_⟩, hne⟩
      by_contra hr
      apply hne
      have hempty : {g : Module.End F V | LinearMap.charpoly g = P} = ∅ := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hr ⟨g, h⟩
      unfold _root_.GlobalTheory.CuspGL.mass
      simp [hempty]
    · rintro ⟨⟨hPS, _⟩, hne⟩
      exact ⟨hPS, hne⟩
  rw [finsum_mem_inter_support_eq _ S I hsupp]
  unfold _root_.GlobalTheory.CuspGL.ipGL _root_.GlobalTheory.CuspGL.mass
  rw [hset, finsum_mem_biUnion ?_ ((Set.finite_range _).subset Set.inter_subset_right)
    (fun _ _ => Set.toFinite _)]
  · refine finsum_mem_congr rfl fun P _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Set.Finite.mem_toFinset] at hg
    show φ g * star (s (LinearMap.charpoly g)) = _
    rw [show LinearMap.charpoly g = P from hg]
  · intro P _ Q _ hPQ
    exact Set.disjoint_left.2 fun g hP hQ => hPQ (hP.symm.trans hQ)

end GlobalTheory.CuspGL
