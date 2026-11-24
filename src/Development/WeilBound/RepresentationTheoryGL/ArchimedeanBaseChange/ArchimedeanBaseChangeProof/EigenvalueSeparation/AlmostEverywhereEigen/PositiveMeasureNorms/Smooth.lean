module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem smooth : ConvCont → Smooth := by
  classical
  intro hconv X ι κ _ u Φ lam c₀ hu hinv hΦ hlam heq
  set f : ι → X.G → ℂ := fun i x => (lam c₀)⁻¹ * ∑ j, ∫ y, Φ c₀ i j y * u j (x * y) ∂X.μ with hf
  have hcont : ∀ i, Continuous (f i) := fun i =>
    continuous_const.mul (continuous_finsetSum _ fun j _ => hconv X _ _ (hΦ c₀ i j) (hu j))
  have hae : ∀ i, f i =ᵐ[X.μ] u i := fun i => (heq c₀ i).mono fun x hx => by
    simp only [hf]
    rw [hx, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  refine ⟨f, fun i => ⟨hcont i, hae i, fun γ hγ x => ?_⟩, fun c i x => ?_⟩
  · simp only [hf]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    funext y
    rw [mul_assoc, hinv j γ hγ]
  · have hconv' : ∀ x, ∑ j, ∫ y, Φ c i j y * f j (x * y) ∂X.μ = ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ := by
      intro x
      refine Finset.sum_congr rfl fun j _ => ?_
      refine integral_congr_ae ?_
      have h1 := (measurePreserving_mul_left X.μ x).quasiMeasurePreserving.ae_eq_comp (hae j)
      filter_upwards [h1] with y hy
      simp only [Function.comp] at hy
      rw [hy]
    have hc1 : Continuous fun x => ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ :=
      continuous_finsetSum _ fun j _ => hconv X _ _ (hΦ c i j) (hu j)
    have hc2 : Continuous fun x => lam c * f i x := continuous_const.mul (hcont i)
    have hae2 : (fun x => ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ) =ᵐ[X.μ] fun x => lam c * f i x := by
      filter_upwards [heq c i, hae i] with x h1 h2
      rw [h1, h2]
    have := (Continuous.ae_eq_iff_eq X.μ hc1 hc2).1 hae2
    rw [hconv' x]
    exact congrFun this x

end PositivityTheory.Rg.BcB.E2.P
