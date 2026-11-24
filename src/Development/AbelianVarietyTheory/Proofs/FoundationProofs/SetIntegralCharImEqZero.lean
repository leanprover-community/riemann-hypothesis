module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical Pointwise

namespace GlobalTheory.UnitaryTheta

theorem setIntegral_mul_char_eq_zero {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V)
    (hF : IsAddFundamentalDomain Λ Fd μ) (f : V → ℂ) (hf : ∀ x y, f (x + y) = f x * f y)
    (hΛ : ∀ y ∈ Λ, f y = 1) (t : V) (ht : f t = -1) : ∫ z in Fd, f z ∂μ = 0 := by
  have hq : MeasurePreserving (fun x => t + x) μ μ := measurePreserving_add_left μ t
  have hF' : IsAddFundamentalDomain Λ ((fun x => t + x) ⁻¹' Fd) μ :=
    hF.preimage_of_equiv hq.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by simp [AddSubgroup.vadd_def, add_left_comm])
  have h1 : ∫ z in (fun x => t + x) ⁻¹' Fd, f z ∂μ = ∫ z in Fd, f z ∂μ :=
    hF'.setIntegral_eq hF (fun g x => by simp [AddSubgroup.vadd_def, hf, hΛ g g.2])
  have h2 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = ∫ z in Fd, f z ∂μ :=
    hq.setIntegral_preimage_emb (measurableEmbedding_addLeft t) f Fd
  have h3 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = - ∫ z in Fd, f z ∂μ := by
    simp only [hf, ht, neg_one_mul, integral_neg, h1]
  linear_combination (h3 - h2) / 2

theorem setIntegral_char_im_eq_zero :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ v : V, v ≠ 0 → (∀ y ∈ Λ, ∃ m : ℤ, (H v y).im = m) → ∫ z in Fd, cexp (2 * π * I * ((H v z).im : ℂ)) ∂μ = 0 := by
  intro V _ _ _ _ _ μ _ H hH Λ _ Fd hF v hv hint
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  have hpos := hH.2 v hv
  set r : ℝ := (H v v).re with hr
  refine setIntegral_mul_char_eq_zero μ Λ Fd hF (fun z => cexp (2 * π * I * ((H v z).im : ℂ)))
    (fun x y => ?_) (fun y hy => ?_) (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v) ?_
  · simp only [map_add (f := _), add_im, ofReal_add, mul_add, Complex.exp_add]
  · obtain ⟨m, hm⟩ := hint y hy
    simp only [hm, ofReal_intCast]
    rw [mul_comm]
    exact Complex.exp_int_mul_two_pi_mul_I m
  · have e : (H v (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v)).im = 1 / 2 := by
      rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, conj_ofReal, conj_I]
      simp only [mul_im, mul_re, ofReal_re, ofReal_im, neg_re, neg_im, I_re, I_im, ← hr]
      field_simp
      ring
    simp only [e]
    rw [← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring

end GlobalTheory.UnitaryTheta
