module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelThird
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Isometry
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.unitMultiplierModel

open Formalism.MainNotions.BigCellDensity Formalism.FourierDecayAlt.P.Dx2.Rad Formalism.L2.SG.monomialWeightModel

variable {r : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1))

local notation "W" => wPt pN

theorem mul_unit_mp (c : ℂ) (h : ‖c‖ = 1) : MeasurePreserving (fun z : ℂ => c * z) volume volume := by
  have hc : c ∈ Submonoid.unitSphere ℂ := by simp [Submonoid.unitSphere, h]
  have key := (rotation (⟨c, hc⟩ : Circle)).measurePreserving
  have e : (fun z : ℂ => c * z) = rotation (⟨c, hc⟩ : Circle) := by
    funext z; rfl
  rw [e]
  exact key

variable (d : Fin (r + 1) → ℂ)

theorem Rm_mp (hd : ∀ a, d a ≠ 0) (hdm : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx W, ‖d (W q.1.1)‖ = ‖d (W q.1.2)‖) :
    MeasurePreserving (Rm pN d) volume volume := by
  have hsw : Function.Involutive (sw pN) := by
    intro q
    exact Subtype.ext (Prod.ext (wPt_invol pN q.1.1) (wPt_invol pN q.1.2))
  let e : Formalism.FourierDecayAlt.C2.Lstidx W ≃ Formalism.FourierDecayAlt.C2.Lstidx W :=
    ⟨sw pN, sw pN, hsw, hsw⟩
  have hG := volume_measurePreserving_piCongrLeft (fun _ : Formalism.FourierDecayAlt.C2.Lstidx W => ℂ) e.symm
  have h : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx W,
      MeasurePreserving (fun z : ℂ => d (W q.1.1) / d (W q.1.2) * star z) volume volume := by
    intro q
    have hu : ‖d (W q.1.1) / d (W q.1.2)‖ = 1 := by
      rw [norm_div, hdm q, div_self]
      exact norm_ne_zero_iff.mpr (hd _)
    exact (mul_unit_mp _ hu).comp Complex.conjLIE.measurePreserving
  have hF := volume_preserving_pi h
  have heq : Rm pN d = (fun (a : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ) (i : Formalism.FourierDecayAlt.C2.Lstidx W) =>
      d (W i.1.1) / d (W i.1.2) * star (a i)) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Formalism.FourierDecayAlt.C2.Lstidx W => ℂ) e.symm) := by
    funext x q
    have hq := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ) e.symm x (e q)
    rw [Equiv.symm_apply_apply] at hq
    change _ = x (sw pN q) at hq
    simp only [Rm, Function.comp_apply, hq]
  rw [heq]
  exact hF.comp hG

end Formalism.L2.SG.unitMultiplierModel

end
