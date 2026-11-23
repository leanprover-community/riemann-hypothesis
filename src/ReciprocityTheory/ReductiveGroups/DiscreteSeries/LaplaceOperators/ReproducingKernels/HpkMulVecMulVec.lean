module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HpkMulVecMulVec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core

open Formalism.QuantumDeterminants

section hpk

variable (k r : ℕ)

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  apply ReciprocityTheory.ChartRestriction.DS.Mult1.TopH.hpk_mulVec <;> assumption

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · have h' : (2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val) := by omega
    rw [hpk_mulVec, if_pos h, hpk_mulVec, if_pos h']
    congr 1
    ext
    simp only
    omega
  · rw [hpk_mulVec, if_neg h, hpk_mulVec, if_neg h]
    split_ifs <;> simp

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec]

end hpk

theorem inv_mul_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r * Hpk k r := by rw [hg']
    _ = 1 := hpk_sq k r

theorem mul_inv_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by
  have h := inv_mul_UH k r hg
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse h)

theorem mul_mem_UH (k r : ℕ) {g x : Mat k r} (hg : g ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    g * x ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

theorem inv_mem_UH (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have e := mul_inv_UH k r hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [e]; simp

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core
