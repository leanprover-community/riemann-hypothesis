module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace GlobalTheory.UnifDens

theorem measurePreserving_comp_equiv {κ : Type} [Fintype κ] {n : ℕ} (e : κ ≃ Fin n) :
    MeasurePreserving (fun x : Fin n → ℂ => fun i : κ => x (e i)) volume volume := by
  have := MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : κ => ℂ) e.symm
  convert this using 1
  funext x i
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : κ => ℂ) e.symm x (e i)
  simp only [Equiv.symm_apply_apply] at this
  exact this.symm

variable {ι : Type} [Fintype ι] {p q n : ℕ}

def flatL (h : Fintype.card (ι × Fin p × Fin q) = n) : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (ι × Fin p × Fin q → ℂ) :=
  (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq h)).toContinuousLinearEquiv

theorem flatL_mp (h : Fintype.card (ι × Fin p × Fin q) = n) :
    MeasurePreserving (flatL h) volume volume := by
  let E' : (Fin n → ℂ) ≃ᵐ ReciprocityTheory.L2DbarEstimates.V n :=
    (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).symm.toHomeomorph.toMeasurableEquiv
  have h1 : MeasurePreserving E' volume volume := GlobalTheory.measurePreserving_toLp_complex
  have h2 : MeasurePreserving E'.symm volume volume := h1.symm
  exact (measurePreserving_comp_equiv (Fintype.equivFinOfCardEq h)).comp h2

end GlobalTheory.UnifDens
