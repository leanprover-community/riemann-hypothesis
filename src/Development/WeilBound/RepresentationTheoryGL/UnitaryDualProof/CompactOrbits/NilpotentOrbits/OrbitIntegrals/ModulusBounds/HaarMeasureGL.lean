module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSubgroupRelIndexMul
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.LocalField.Basic
public import GroundTheory.AutomorphicForms.MeasuresModulus
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section

open Matrix Module ValuativeRel MeasureTheory

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

theorem measure_eq_relIndex_mul' (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G) (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) (hi : H.relIndex K ≠ 0) :
    μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  apply GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul <;> assumption

theorem relIndex_ne_zero_of_isCompact_of_isOpen' {X : Type} [TopologicalSpace X] [AddCommGroup X]
    [IsTopologicalAddGroup X] (A H : AddSubgroup X) (hA : IsCompact (A : Set X)) (hH : IsOpen (H : Set X))
    (_hle : H ≤ A) : H.relIndex A ≠ 0 := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hopen : IsOpen ((H.addSubgroupOf A : AddSubgroup A) : Set A) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (A ⧸ H.addSubgroupOf A) :=
    AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact AddSubgroup.index_ne_zero_of_finite

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ratio_pi {d : ℕ} (X' Y' : AddSubgroup (Fin d → k)) (hXc : IsCompact (X' : Set (Fin d → k)))
    (hXo : IsOpen (X' : Set (Fin d → k))) (L : (Fin d → k) ≃ₗ[k] (Fin d → k))
    (hY : (Y' : Set (Fin d → k)) = L '' (X' : Set (Fin d → k))) :
    (X' ⊓ Y').relIndex X' ≠ 0 ∧ (X' ⊓ Y').relIndex Y' ≠ 0 ∧
      ((X' ⊓ Y').relIndex Y' : ℝ) / ((X' ⊓ Y').relIndex X' : ℝ) =
        (distribHaarChar k (LinearEquiv.det L) : ℝ) := by
  have hLc : Continuous L := L.toLinearMap.continuous_on_pi
  have hLsc : Continuous L.symm := L.symm.toLinearMap.continuous_on_pi
  have hYeq : (Y' : Set (Fin d → k)) = L.symm ⁻¹' (X' : Set (Fin d → k)) := by
    rw [hY]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro h
      exact ⟨L.symm y, h, by simp⟩
  have hYo : IsOpen (Y' : Set (Fin d → k)) := hYeq ▸ hXo.preimage hLsc
  have hYc : IsCompact (Y' : Set (Fin d → k)) := hY ▸ hXc.image hLc
  have hJo : IsOpen ((X' ⊓ Y' : AddSubgroup (Fin d → k)) : Set (Fin d → k)) := by
    rw [AddSubgroup.coe_inf]; exact hXo.inter hYo
  have n1 := relIndex_ne_zero_of_isCompact_of_isOpen' X' (X' ⊓ Y') hXc hJo inf_le_left
  have n2 := relIndex_ne_zero_of_isCompact_of_isOpen' Y' (X' ⊓ Y') hYc hJo inf_le_right
  refine ⟨n1, n2, ?_⟩
  borelize (Fin d → k)
  let μ : Measure (Fin d → k) := Measure.addHaar
  have e1 := measure_eq_relIndex_mul' _ μ (X' ⊓ Y') X' inf_le_left hJo.measurableSet n1
  have e2 := measure_eq_relIndex_mul' _ μ (X' ⊓ Y') Y' inf_le_right hJo.measurableSet n2
  have e3 : μ (Y' : Set (Fin d → k)) = distribHaarChar (Fin d → k) L * μ (X' : Set (Fin d → k)) := by
    rw [distribHaarChar_mul μ L, hY]
    rfl
  rw [GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq] at e3
  have hJ0 : μ ((X' ⊓ Y' : AddSubgroup (Fin d → k)) : Set (Fin d → k)) ≠ 0 :=
    hJo.measure_ne_zero μ ⟨0, (X' ⊓ Y').zero_mem⟩
  have hJt : μ ((X' ⊓ Y' : AddSubgroup (Fin d → k)) : Set (Fin d → k)) ≠ ⊤ :=
    ne_top_of_le_ne_top hXc.measure_lt_top.ne (measure_mono (by simp [AddSubgroup.coe_inf]))
  have key : ((X' ⊓ Y').relIndex Y' : ENNReal) =
      (distribHaarChar k (LinearEquiv.det L) : ENNReal) * ((X' ⊓ Y').relIndex X' : ENNReal) := by
    have h := e3
    rw [e1, e2, ← mul_assoc] at h
    exact (ENNReal.mul_left_inj hJ0 hJt).1 h
  have key' := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_mul] at key'
  simp only [ENNReal.toReal_natCast, ENNReal.coe_toReal] at key'
  rw [key', mul_div_assoc, div_self (by exact_mod_cast n1), mul_one]

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
