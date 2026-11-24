module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.PeriodIntegrals.QuotInv
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem Hpk_ne_zero' (k r : ℕ) : Hpk k r ≠ 0 := by
  intro h
  have h1 : Hpk k r ⟨r + k, by omega⟩ ⟨r + k, by omega⟩ = -1 := by
    simp [Hpk]
  rw [h] at h1
  simp at h1

theorem IsClosedSub.mul_inv {S : Set (Mat k r)} (hS : IsClosedSub k r S) {a : Mat k r} (ha : a ∈ S) :
    a * a⁻¹ = 1 := by
  by_cases hd : IsUnit a.det
  · exact Matrix.mul_nonsing_inv a hd
  · exfalso
    have h0 : a⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit a hd
    have hm : a⁻¹ ∈ GG k r := hS.1 (hS.2.2.2.2 a ha)
    rw [h0] at hm
    have : (0 : Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := hm
    simp at this
    exact Hpk_ne_zero' k r this.symm

theorem IsClosedSub.isMatGroup {S : Set (Mat k r)} (hS : IsClosedSub k r S) : PI.IsMatGroup S :=
  ⟨hS.2.1, hS.2.2.1, hS.2.2.2.1, fun a ha => ⟨hS.2.2.2.2 a ha, hS.mul_inv ha⟩⟩

theorem haarOn_locFinite_openPos :
    ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn S μ →
      (∀ C : Set (Mt k r), IsCompact C → μ C < ⊤) ∧
      (∀ U : Set (Mt k r), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ S) → 0 < μ U) := by
  intro k r S μ hS hμ
  have hμ' : PI.IsHaarOnM S μ := hμ
  obtain ⟨-, hK, hU⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ S μ hS.isMatGroup hμ'
  refine ⟨fun C hC => ?_, hU⟩
  have hA : IsClosed {x : Mt k r | Matrix.of x ∈ S} := hS.2.1
  have h1 : μ C ≤ μ (C ∩ {x : Mt k r | Matrix.of x ∈ S}) + μ (C \ {x : Mt k r | Matrix.of x ∈ S}) :=
    measure_le_inter_add_sdiff μ C _
  have h2 : μ (C \ {x : Mt k r | Matrix.of x ∈ S}) = 0 :=
    measure_mono_null (fun x hx => hx.2) hμ.2.2.1
  have h3 : μ (C ∩ {x : Mt k r | Matrix.of x ∈ S}) < ⊤ :=
    hK _ (hC.inter_right hA) (fun x hx => hx.2)
  rw [h2, add_zero] at h1
  exact lt_of_le_of_lt h1 h3

end GlobalTheory.SgInf
