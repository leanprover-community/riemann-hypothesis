module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

private lemma pi_single_eq_re_smul_add_im_smul {g : ℕ} (a : Fin g) (w : ℂ) :
    (Pi.single a w : Fin g → ℂ) =
      (w.re : ℝ) • (Pi.single a 1 : Fin g → ℂ) + (w.im : ℝ) • (I • (Pi.single a 1 : Fin g → ℂ)) := by
  ext j
  by_cases hj : j = a
  · subst hj
    apply Complex.ext <;> simp
  · simp [hj]

theorem map_I_smul_of_cauchyRiemann {g : ℕ} (L : (Fin g → ℂ) →L[ℝ] ℂ)
    (h : ∀ a, L (Pi.single a 1 : Fin g → ℂ) + I * L (I • (Pi.single a 1 : Fin g → ℂ)) = 0)
    (c : ℂ) (v : Fin g → ℂ) : L (c • v) = c • L v := by

  have hI : ∀ a, L (I • (Pi.single a 1 : Fin g → ℂ)) = I * L (Pi.single a 1) := by
    intro a
    linear_combination (-I) * h a + L (I • (Pi.single a 1 : Fin g → ℂ)) * I_sq
  have hline : ∀ a (w : ℂ), L (Pi.single a w : Fin g → ℂ) = w * L (Pi.single a 1) := by
    intro a w
    rw [pi_single_eq_re_smul_add_im_smul a w, map_add (f := _), map_smul, map_smul, hI a]
    conv_rhs => rw [← Complex.re_add_im w]
    simp only [Complex.real_smul]
    ring
  have hsum : ∀ u : Fin g → ℂ, L u = ∑ a, u a * L (Pi.single a 1) := by
    intro u
    conv_lhs => rw [← Finset.univ_sum_single u]

    rw [map_sum]
    exact Finset.sum_congr rfl (fun a _ => hline a (u a))
  rw [hsum, hsum v, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem cauchyRiemann_iff_differentiableOn_complex :
    ∀ (g : ℕ) (U : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℂ), IsOpen U → (DifferentiableOn ℝ f U → ((∀ a, ∀ z ∈ U, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = 0) ↔ DifferentiableOn ℂ f U)) ∧ (DifferentiableOn ℂ f U → ContDiffOn ℝ ∞ f U ∧ ∀ v, DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U) := by
  intro g U f hU
  refine ⟨fun hR => ⟨fun hCR => ?_, fun hC => ?_⟩, fun hC => ?_⟩
  ·
    intro z hz
    have hzR : DifferentiableAt ℝ f z := hR.differentiableAt (hU.mem_nhds hz)
    set L := fderiv ℝ f z with hL
    have hlin : ∀ (c : ℂ) (v : Fin g → ℂ), L (c • v) = c • L v :=
      map_I_smul_of_cauchyRiemann L (fun a => hCR a z hz)
    let L' : (Fin g → ℂ) →L[ℂ] ℂ :=
      { toFun := L
        map_add' := L.map_add
        map_smul' := hlin
        cont := L.continuous }
    have hres : L'.restrictScalars ℝ = L := by
      ext v; rfl
    exact (hasFDerivAt_of_restrictScalars ℝ hzR.hasFDerivAt hres).differentiableAt.differentiableWithinAt
  · intro a z hz
    have hzC : DifferentiableAt ℂ f z := hC.differentiableAt (hU.mem_nhds hz)
    rw [hzC.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
    rw [← mul_assoc, I_mul_I]
    ring
  · refine ⟨?_, fun v => SCV.differentiableOn_fderiv_apply hU hC v⟩
    exact (SCV.contDiffOn_of_differentiableOn hU hC ∞).restrict_scalars ℝ

end GlobalTheory
