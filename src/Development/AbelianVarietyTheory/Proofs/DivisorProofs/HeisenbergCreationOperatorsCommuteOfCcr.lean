module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergAnnihilationCreationCommutatorEqDelta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem fockM_comm_sum {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (j k : W × (Ix P Q × Ix R S)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAt j z w a b * star (unitAt k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  apply GlobalTheory.CCRFock.CommDM.sum_unitAt <;> assumption

theorem fockM_comm : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ j k : W × (Ix P Q × Ix R S), GlobalTheory.CCRFock.fockM H j * GlobalTheory.CCRFock.fockM H k = GlobalTheory.CCRFock.fockM H k * GlobalTheory.CCRFock.fockM H j := by
  intro V _ _ W _ _ P Q R S H _ _ hc j k
  have h11 := hc (unitAt j 1) (unitAt k 1)
  have h1i := hc (unitAt j 1) (unitAt k Complex.I)
  have hi1 := hc (unitAt j Complex.I) (unitAt k 1)
  have hii := hc (unitAt j Complex.I) (unitAt k Complex.I)
  rw [fockM_comm_sum] at h11 h1i hi1 hii
  by_cases hjk : j = k
  · rw [hjk]
  · simp only [if_neg hjk, Complex.zero_im, Complex.ofReal_zero, mul_zero, zero_smul, sub_eq_zero] at h11 h1i hi1 hii
    unfold fockM
    have c : Commute (H (unitAt j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I))
        (H (unitAt k 1) - (lineSign k.2.1 k.2.2 * Complex.I) • H (unitAt k Complex.I)) :=
      Commute.sub_left (Commute.sub_right h11 (Commute.smul_right h1i _))
        (Commute.smul_left (Commute.sub_right hi1 (Commute.smul_right hii _)) _)
    exact ((c.smul_left _).smul_right _).eq

end GlobalTheory.CCRFock
