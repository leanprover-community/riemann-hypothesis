module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleD
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleE
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

namespace LTF

open PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE

theorem Mlift_rowW {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K))
    (hL : GoodL h lam sg sz L) (I : ∀ k, Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW N N) (Mlift h lam sg sz hsz L I) (liftWt h lam sg (tupCnt I)) := by
  classical
  have hH : IsWeightedHomogeneous (rowW N N) (Mlift h lam sg sz hsz L I)
      (w0r h lam sg + ∑ k, wk h (I k) (k ∈ L)) :=
    (constant_weighted_homogeneous h lam sg).mul (IsWeightedHomogeneous.prod _ _ _ (fun k _ => G_rowW h sz hsz L k (I k)))
  convert hH using 1
  funext a
  obtain ⟨av, hav⟩ := a
  simp only [Pi.add_apply, Finset.sum_apply, wk, constant_weight_apply, Pi.single_apply, ite_apply, Pi.zero_apply,
    Finset.sum_add_distrib, liftWt]
  by_cases ha : av < n
  · have hn : 0 < n := by omega
    rw [dite_eq_left ha, dite_eq_left (by omega), dite_eq_left hn, if_pos ha, if_neg (by omega)]
    have hS2 : (∑ k : Fin K, if k ∈ L then (if (⟨av, hav⟩ : Fin N) = ⟨N - 1, by omega⟩ then 1 else 0) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hne : (⟨av, hav⟩ : Fin N) ≠ ⟨N - 1, by omega⟩ := fun e => by rw [Fin.mk.injEq] at e; omega
      simp [hne]
    have hS1 : (∑ k : Fin K, ∑ q : Fin (sz k), if (⟨av, hav⟩ : Fin N) = eRow h (I k q) then 1 else 0) =
        tupCnt I ⟨av, ha⟩ := by
      simp only [tupCnt, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro q _
      have : ((⟨av, hav⟩ : Fin N) = eRow h (I k q)) ↔ (I k q = ⟨av, ha⟩) := by
        simp only [eRow, Fin.ext_iff]; exact eq_comm
      by_cases hq : I k q = ⟨av, ha⟩
      · rw [if_pos (this.2 hq), if_pos hq]
      · rw [if_neg (fun e => hq (this.1 e)), if_neg hq]
    rw [hS1, hS2]
    have e3 := aLast_val h lam sg hI hn
    have e4 := sg_detShift sg hn
    have e5 := lam_detShift h lam
    omega
  · have hav' : av = n := by omega
    simp only [dif_neg ha, if_neg ha, if_pos hav', mul_zero, mul_one]
    have hS1 : (∑ k : Fin K, ∑ q : Fin (sz k), if (⟨av, hav⟩ : Fin N) = eRow h (I k q) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero; intro k _
      apply Finset.sum_eq_zero; intro q _
      rw [if_neg]
      intro e
      simp only [eRow, Fin.ext_iff] at e
      have := (I k q).2
      omega
    have hS2 : (∑ k : Fin K, if k ∈ L then (if (⟨av, hav⟩ : Fin N) = ⟨N - 1, by omega⟩ then 1 else 0) else 0) =
        L.card := by
      rw [Finset.sum_congr rfl (g := fun k => if k ∈ L then 1 else 0)]
      · rw [← Finset.card_filter]; congr 1; ext k; simp
      · intro k _
        rw [if_pos (Fin.ext (by simp; omega))]
    rw [hS1, hS2, cardL h lam sg sz hsz hshape L hL]
    have hsplit : (∑ i : Fin n, (bb h lam sg i).toNat) =
        (∑ i : Fin n, if i.1 = 0 then (bb h lam sg i).toNat else 0) +
          ∑ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [sum_ite_val (fun i : Fin n => (bb h lam sg i).toNat) 0] at hsplit
    have e6 := sumB h lam sg hI
    unfold dLast
    split_ifs at hsplit ⊢ with h1 h2 <;> omega

end LTF

theorem tuple_decomposition_formula : TupleCore := by
  intro n N h lam sg hI K sz hsz hshape
  obtain ⟨L, hL⟩ := LTD.goodL_exists h lam sg hI sz hshape
  obtain ⟨htop, hstd1, hstd2, hstd3⟩ := LTB.top_component_formula n N h lam sg hI K sz hsz hshape L hL
  refine ⟨LTM.Mlift h lam sg sz hsz L, fun I => ⟨?_, LTF.Mlift_rowW h lam sg hI sz hsz hshape L hL I,
    LTF.bidet_rowW sz hsz I⟩, fun I w hw => LTC.word_clause h lam sg sz hsz L I w hw, htop,
    ⟨LTM.stdT sz hsz, hstd1, hstd2, hstd3⟩⟩
  have hm := LTE.Mlift_mem_colWt h lam sg sz hsz L I
  rw [LTE.colWt_eq h lam sg hI sz hsz hshape L hL] at hm
  exact hm

end PI.WGL
