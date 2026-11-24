module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DeuringHeilbronnM
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplDefs
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplBox
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLF
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplMainA
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplMainB
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplPick
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem smoothed_explicit_formula : ExplicitS := by
  intro κ hκ hκ'
  obtain ⟨C₁, hC₁, hch⟩ := ex_choose
  obtain ⟨C₄, hC₄, hbox⟩ := ex_box
  obtain ⟨C₂, C₃, hC₂, hC₃, hcore⟩ := exm_core
  set G := 6 * C₁ * C₂ / κ with hG
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  set AL := 3 * (G + 4 / (3 * κ)) * (2 / κ) with hAL
  set AW := (1 + 2 * C₃) + (3 * (G + 1) + 3 * (G + 1)) with hAW
  set C := max (max 4 C₄) (max AL AW) with hC
  have hC4 : 4 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCC₄ : C₄ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCL : AL ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCW : AW ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, by linarith, ?_⟩
  intro M _ χ T hM hT
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨σ₁, T', δ, hσ, hσ', hTT', hT'T, hδ0, hδ', hδlow, hgapre, hgapim⟩ := hch κ hκ hκ' M χ T hM hT
  obtain ⟨Z₀, hZ₀, hwin, _⟩ := hbox M χ (T + 1) hM (by linarith)
  have hZ : ∀ ρ : ℂ, ρ ∈ Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T') ↔
      (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T') := by
    intro ρ
    rw [Finset.mem_filter, hZ₀]
    constructor
    · rintro ⟨⟨h0, _, _⟩, h1, h2⟩
      exact ⟨h0, h1, h2⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, by linarith, by linarith⟩, h1, h2⟩
  refine ⟨Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T'), exOrd χ, explicitFormulaConstant χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨h0, h1, h2⟩ := (hZ ρ).1 hρ
    exact ⟨(isLZero_iff_exLF χ ρ).2 h0, by linarith, by linarith⟩
  · intro ρ hρ hre him
    have h0 := (isLZero_iff_exLF χ ρ).1 hρ
    refine (hZ ρ).2 ⟨h0, by linarith, ?_⟩
    have h2 := hgapim ρ h0 (by linarith)
    rcases (him.trans hTT').lt_or_eq with h | h
    · exact h
    · rw [h] at h2; simp at h2; linarith
  · intro ρ hρ
    exact exOrd_pos χ ((hZ ρ).1 hρ).1
  · intro ρ hρ hd
    have h0 := ((hZ ρ).1 hρ).1
    exact exOrd_eq_one χ h0 (exLF_deriv_ne_zero χ h0 hd)
  · intro t
    have hsub : (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1) ⊆
        Z₀.filter (fun ρ => |ρ.im - t| ≤ 1) :=
      Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    have h1 : (∑ ρ ∈ (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1),
        exOrd χ ρ) ≤ ∑ ρ ∈ Z₀.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ :=
      Finset.sum_le_sum_of_subset hsub
    have h2 : (0 : ℝ) ≤ Real.log ((M : ℝ) * (|t| + 2)) := by
      apply Real.log_nonneg
      have := abs_nonneg t
      nlinarith
    calc ((∑ ρ ∈ (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1),
        exOrd χ ρ : ℕ) : ℝ) ≤ ((∑ ρ ∈ Z₀.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ ≤ C₄ * Real.log ((M : ℝ) * (|t| + 2)) := hwin t
      _ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) := by gcongr
  · intro y hy
    have hmain := hcore κ hκ hκ' M χ T σ₁ T' δ hM hT hσ hσ' hTT' hT'T hδ0 hδ' hgapre hgapim _ hZ y hy
    refine hmain.trans ?_
    have hl1 := exm_log_ge_one (M : ℝ) T hM' hT
    have hNle := exm_N_le κ C₁ C₂ (M : ℝ) T δ hκ hC₁ hC₂ hM' hT hδ0 hδlow
    rw [← hG] at hNle
    set N := C₂ * (2 * Real.log ((M : ℝ) * T)) / δ with hN
    have hN0 : 0 ≤ N := by rw [hN]; positivity
    have ht := exm_tail_num C₃ T T' y (Real.log ((M : ℝ) * T)) hC₃ hT hTT' hy hl1
    have hh := exm_horiz_num G N T T' y (Real.log ((M : ℝ) * T)) hG0 hN0 hNle hT hTT' hy hl1
    have hl := exm_left_num κ G N (M : ℝ) T T' σ₁ y hκ hκ' hG0 hN0 hNle hM' hT hTT' hT'T hσ hσ' hy
    have hy0 : 0 < y := by linarith
    have hly := exm_log_y y hy
    have hX : 1 ≤ (M : ℝ) * T := by nlinarith
    have hfin := sum_le_mul_rpow_add AL AW C ((M : ℝ) * T) (y ^ (-(κ / 2)))
      (Real.log y * Real.log ((M : ℝ) * T) ^ 2 / T) hC4 hCL hCW hX (Real.rpow_nonneg hy0.le _)
      (by have : 0 < T := by linarith
          positivity)
    refine le_trans ?_ hfin
    have hsum := add_le_add (add_le_add ht hl) (add_le_add hh hh)
    calc _ = _ := by ring
      _ ≤ _ := hsum
      _ = _ := by rw [hAW, hAL]; ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
