module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateGramSymm
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.CasimirOrder

namespace GlobalTheory.CasimirOrder

open Matrix

theorem casimir_central : ∀ {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ),
    (∀ a b, s (a * b) = s b * s a) → (∀ a, s (s a) = a) → (∀ a b, φ (a * b) = φ (b * a)) →
    (∀ a, φ (s a) = φ a) → (∀ a, a ≠ 0 → 0 < φ (s a * a)) →
    ∀ a, a * casimir (⇑x) s φ = casimir (⇑x) s φ * a := by
  intro O _ r x s φ hs hss hφc hφs hpos a
  classical
  set b := form s φ with hbdef
  have hb : ∀ u v, b u v = b v u := form_symm hs hss hφs
  set G := gram (⇑x) s φ with hGdef
  have hA : ∀ i j, G.adjugate i j = G.adjugate j i := adjugate_gram_symm hs hss hφs
  have hds : ∀ v, G.det • v = ∑ i, ∑ j, (G.adjugate i j * b (x i) v) • x j :=
    det_smul_eq_sum x b hb
  have hδ : G.det ≠ 0 := by
    have h := (posDef_gram x b hb (fun w hw => hpos w hw)).det_pos
    rw [← Int.cast_det] at h
    exact_mod_cast h.ne'
  haveI : Module.Free ℤ O := Module.Free.of_basis x
  have htf : Function.Injective (fun v : O => G.det • v) := smul_right_injective O hδ
  have hbid : ∀ u v, b u (v * s a) = b v (u * a) := by
    intro u v
    rw [hb v]
    simp only [hbdef, form_apply]
    rw [hs, ← mul_assoc, hφc, ← mul_assoc]
  set A := G.adjugate with hAdef
  set F : Fin r → Fin r → Fin r → Fin r → O :=
    fun i j k l => (A i j * (A k l * b (x k) (x i * s a))) • (s (x l) * x j) with hF
  have key1 : ∀ i j, G.det • (A i j • (a * (s (x i) * x j))) = ∑ k, ∑ l, F i j k l := by
    intro i j
    have e : a * (s (x i) * x j) = s (x i * s a) * x j := by rw [hs, hss, mul_assoc]

    rw [e, smul_comm, show G.det • (s (x i * s a) * x j) = s (G.det • (x i * s a)) * x j by
    rw [map_zsmul, smul_mul_assoc], hds, map_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_

    rw [map_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, smul_mul_assoc, smul_smul]
  have key2 : ∀ p q, G.det • (A p q • (s (x p) * x q * a)) = ∑ i, ∑ j, F i j q p := by
    intro p q
    rw [smul_comm, mul_assoc, ← mul_smul_comm, hds, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_smul, hF, hA p q, ← hbid]
    ring_nf
  apply htf
  simp only
  have L : G.det • (a * casimir (⇑x) s φ) = ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by
    unfold casimir
    rw [← hGdef, ← hAdef, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, key1]
  have R : G.det • (casimir (⇑x) s φ * a) = ∑ l, ∑ k, ∑ i, ∑ j, F i j k l := by
    unfold casimir
    rw [← hGdef, ← hAdef, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_mul_assoc, key2]
  rw [L, R]
  calc ∑ i, ∑ j, ∑ k, ∑ l, F i j k l = ∑ i, ∑ k, ∑ j, ∑ l, F i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, F i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, F i j k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ i, ∑ j, F i j k l := Finset.sum_comm

end GlobalTheory.CasimirOrder
