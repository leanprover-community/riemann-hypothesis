module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import Mathlib.RingTheory.TensorProduct.Maps
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

namespace GlobalTheory


open Filter Topology in
open Filter Topology TopologicalSpace TensorProduct in
theorem _root_.GlobalTheory.tensor_hol_ext_of_values :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (D : Type) [CommRing D] [Algebra ℂ D] (x y : D ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol W), (∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x = Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) y) → x = y := by
  intro E _ _ W D _ _ x y h
  classical
  rw [← sub_eq_zero]
  set z := x - y with hz
  have hzp : ∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D)
      ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp))
      (fun _ _ ↦ Commute.all _ _) z = 0 := fun p hp => by
    rw [hz, map_sub, h p hp, sub_self]
  let b := Module.Free.chooseBasis ℂ D
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := _root_.GlobalTheory.AnPer.Hol W) b
  have hc : ∀ i, e z i = 0 := by
    intro i
    apply _root_.GlobalTheory.AnPer.Hol.ext_fn
    intro p hp
    have hzero : (0 : _root_.GlobalTheory.AnPer.Hol W).fn p = 0 := by
      rw [← _root_.GlobalTheory.AnPer.Hol.ev_apply p hp, map_zero]
    have h0 := hzp p hp

    rw [← e.symm_apply_apply z, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum,
    map_sum] at h0
    simp only [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
      _root_.GlobalTheory.AnPer.Hol.ev_apply, Algebra.ofId_apply] at h0
    have h1 : ∑ j ∈ (e z).support, (e z j).fn p • b j = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    by_cases hi : i ∈ (e z).support
    · rw [linearIndependent_iff'.1 b.linearIndependent (e z).support (fun j => (e z j).fn p) h1 i hi,
        hzero]
    · rw [Finsupp.notMem_support_iff.1 hi]
  exact e.injective (by rw [map_zero]; exact Finsupp.ext hc)

end GlobalTheory
