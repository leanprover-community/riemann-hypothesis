module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

@[expose] public section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem levelOne_form_one_add_expDecay :
    ∀ d : ℤ, 4 ≤ d → Even d → ∃ e : ℍ → ℂ, IsMF ⊤ d e ∧
      (fun τ : ℍ => e τ - 1) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  intro d hd hev
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ d)
  have hk : 3 ≤ k := by omega
  have hk2 : Even k := by simpa [Int.even_coe_nat] using hev
  let f : ModularForm 𝒮ℒ (k : ℤ) := ModularForm.E hk
  refine ⟨f, isMF_coe_top f, ?_⟩
  have h0 : valueAtInfty (f : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)]
    exact EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  have h := exp_decay_sub_atImInfty one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  rw [h0] at h
  simpa using h

end GlobalTheory
