module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.DiamondOperatorFamilies

theorem isDiamondMatrixAtLevel_of_gamma1Gamma0 {N l d : ℕ} (hl : l.Prime) (hlN : ¬ l ∣ N) {γ : SL(2, ℤ)} (h : GlobalTheory.KZ.IsDiam N l d γ) :
    GlobalTheory.HeckeFamilyMatrices.IsDiam N l (d : ZMod N) γ := by
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hc : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN).symm
  have h0' : γ ∈ CongruenceSubgroup.Gamma0 N := h0
  have h1' : γ ∈ CongruenceSubgroup.Gamma0 l := h1
  refine ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem] at h0' h1' ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0' h1' ⊢
    push_cast
    exact IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 hc) h0' h1'
  · simpa [en, GlobalTheory.HeckeFamilyMatrices.mat] using h2

theorem sgD_fams : ∀ (N l : ℕ), 0 < N → l.Prime → ¬ l ∣ N → (∀ d : ℕ, Nat.Coprime d N → GlobalTheory.HeckeFamilyMatrices.IsDiam N l (d : ZMod N) (sgD N l d)) ∧ (∀ q : ℕ, opL ℂ N l (Letter.T q) = ∑ i, opP ℂ (GlobalTheory.HeckeFamilyMatrices.tqFam q (sgD N l q) i)) ∧ opL ℂ N l Letter.U = ∑ i, opP ℂ (GlobalTheory.HeckeFamilyMatrices.ulFam l i) ∧ ∀ d : ℕ, opL ℂ N l (Letter.D d) = ∑ _i : Unit, opP ℂ (GlobalTheory.HeckeFamilyMatrices.mat (sgD N l d)) := by
  intro N l hN hl hlN
  refine ⟨fun d hd => isDiamondMatrixAtLevel_of_gamma1Gamma0 hl hlN (Betti.isDiam_sgD hN.ne' hl.ne_zero hd), fun q => ?_, ?_, fun d => ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [opL, Finset.sum_range, GlobalTheory.HeckeFamilyMatrices.tqFam, Fin.coe_castSucc, Fin.is_lt, if_true, Fin.val_last,
      lt_irrefl, if_false, GlobalTheory.HeckeFamilyMatrices.dg, GlobalTheory.HeckeFamilyMatrices.mat]
  · simp only [opL, Finset.sum_range, GlobalTheory.HeckeFamilyMatrices.ulFam]
  · simp [opL, GlobalTheory.HeckeFamilyMatrices.mat]

end GlobalTheory.KZ.DiamondOperatorFamilies
