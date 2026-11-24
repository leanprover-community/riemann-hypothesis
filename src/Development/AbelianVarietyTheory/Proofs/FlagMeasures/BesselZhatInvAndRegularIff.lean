module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.RegInv

theorem hpk_isUnit_det (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h : (Hpk k r).det * (Hpk k r).det = 1 := by
    rw [← Matrix.det_mul, GBasic.Hpk_sq, Matrix.det_one]
  exact ⟨⟨_, _, h, h⟩, rfl⟩

private lemma unit_lemma' {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) : IsUnit γ.det ∧ γ⁻¹ ∈ GG k r :=
  (unitary_group_holds _ (Hpk k r) (hpk_isUnit_det k r)).2.2 γ h

theorem inv_mem {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) : γ⁻¹ ∈ GG k r := (unit_lemma' h).2

private lemma herm_mulVec_eq_of_mem_GG {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (γ *ᵥ x) (γ *ᵥ y) = herm (Hpk k r) x y := by
  have hγ : γᴴ * Hpk k r * γ = Hpk k r := h
  simp only [herm]
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hγ]

private lemma herm_Hpk_swap (k r : ℕ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (herm (Hpk k r) y x) := by
  simp only [herm]
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, GBasic.Hpk_herm]

theorem herm_inv {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (γ⁻¹ *ᵥ v) w = star (herm (Hpk k r) (γ *ᵥ w) v) := by
  have hv : γ *ᵥ (γ⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_lemma' h).1, Matrix.one_mulVec]
  rw [← herm_mulVec_eq_of_mem_GG h (γ⁻¹ *ᵥ v) w, hv]
  exact herm_Hpk_swap k r _ _

theorem zhat_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r) :
    Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ := by
  ext a b
  simp only [Zhat, Matrix.conjTranspose_apply]
  exact herm_inv h _ _

theorem dmin_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r)
    (l : Fin (r + 2)) : Dmin k r z' z γ⁻¹ l = star (Dmin k r z z' γ l) := by
  simp only [Dmin]
  rw [zhat_inv z z' h, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]

theorem gf_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r) :
    Gf k r z' z γ⁻¹ = Gf k r z z' γ := by
  simp only [Gf, dmin_inv z z' h, Complex.star_def, Complex.normSq_conj]
  ring

theorem zhat_inv_and_reg (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (h : γ ∈ GG k r) :
    Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ ∧ (γ ∈ Greg k r z z' ↔ γ⁻¹ ∈ Greg k r z' z) := by
  refine ⟨zhat_inv z z' h, ?_⟩
  simp only [Greg, Set.mem_ofPred_eq, dmin_inv z z' h, gf_inv z z' h, star_ne_zero, h, inv_mem h,
    true_and]

end GlobalTheory.SgInf.RegInv
