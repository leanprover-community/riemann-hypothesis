module

import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.MomentRecursion.MomStep
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.MomB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

open MeasureTheory Set

namespace PositivityTheory.RgFd

theorem mom_step {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {ν : Measure Ω} {ν' : Measure Ω'} {V : Ω → ℝ}
    {V' : Ω' → ℝ} (hV : Measurable V) (hV' : Measurable V') (h0 : ∀ x, 0 ≤ V x ∧ V x ≤ 1) (h0' : ∀ y, 0 ≤ V' y ∧ V' y ≤ 1)
    (he : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j) ∂ν')
    (hf : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν ≠ ⊤) (M : ℕ) : ∀ j : ℕ, 1 ≤ j →
    ∫⁻ x, ENNReal.ofReal (V x ^ j * (1 - V x) ^ M) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j * (1 - V' y) ^ M) ∂ν' := by
  apply CompanionTheory.RgFd.mom_step <;> assumption

theorem mom_sum {A : Type} [MeasurableSpace A] (m : Measure A) {W : A → ℝ} (hW : Measurable W) (h : ∀ x, 0 ≤ W x ∧ W x ≤ 1) :
    m {x | 0 < W x} = ∑' M : ℕ, ∫⁻ x, ENNReal.ofReal (W x ^ 1 * (1 - W x) ^ M) ∂m := by
  rw [← lintegral_tsum fun M => (by fun_prop : Measurable fun x => ENNReal.ofReal (W x ^ 1 * (1 - W x) ^ M)).aemeasurable,
    ← lintegral_indicator_one (measurableSet_lt measurable_const hW)]
  refine lintegral_congr fun x => ?_
  have a := (h x).1
  have b := sub_nonneg.2 (h x).2
  by_cases hx : 0 < W x
  · have hs : HasSum (fun M : ℕ => W x ^ 1 * (1 - W x) ^ M) (W x ^ 1 * (1 - (1 - W x))⁻¹) :=
      (hasSum_geometric_of_lt_one b (by linarith)).mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun M => by positivity) hs.summable, hs.tsum_eq,
      indicator_of_mem (show x ∈ {x | 0 < W x} from hx)]
    simp [mul_inv_cancel₀ hx.ne']
  · rw [indicator_of_notMem (show x ∉ {x | 0 < W x} from hx), show W x = 0 from le_antisymm (not_lt.1 hx) a]
    simp

theorem momA : MomA := by
  intro Ω Ω' _ _ ν ν' U U' t0 hU hU' h h' ht he hf
  have p : ∀ {A : Type} (W : A → ℝ), (∀ x, 0 ≤ W x ∧ W x ≤ 1) → {x | 0 < W x} = {x | 0 < W x ^ t0} := fun W h => by
    ext x
    show 0 < W x ↔ 0 < W x ^ t0
    exact ⟨fun a => pow_pos a _, fun a => (h x).1.lt_of_ne fun b => by
      rw [← b, zero_pow (by omega)] at a; exact lt_irrefl _ a⟩
  have q : ∀ {A : Type} (W : A → ℝ), (∀ x, 0 ≤ W x ∧ W x ≤ 1) → ∀ x, 0 ≤ W x ^ t0 ∧ W x ^ t0 ≤ 1 := fun W h x =>
    ⟨pow_nonneg (h x).1 _, pow_le_one₀ (h x).1 (h x).2⟩
  rw [p U h, p U' h', mom_sum ν (hU.pow_const t0) (q U h), mom_sum ν' (hU'.pow_const t0) (q U' h')]
  refine tsum_congr fun M => mom_step (hU.pow_const t0) (hU'.pow_const t0) (q U h) (q U' h') (fun j hj => ?_)
    (fun j hj => ?_) M 1 le_rfl
  · simpa only [← pow_mul, mul_comm t0] using he j hj
  · simpa only [← pow_mul, mul_comm t0] using hf j hj

theorem momB : MomB := by
  apply CompanionTheory.RgFd.momB <;> assumption

theorem momW_of : MomA → MomB → MomW := by
  intro hA hB Ω _ P h U I _ α β c t0 hh hU h01 hα hβ hc hm
  obtain ⟨ν', U', m', p', e'⟩ := hB I α β c hα hβ hc
  have e : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (U x ^ (j * (t0 + 1))) ∂(P.withDensity h) =
      ENNReal.ofReal (c / ∏ i, (α i + (j * (t0 + 1) : ℕ) * β i)) := fun j hj => by
    rw [lintegral_withDensity_eq_lintegral_mul _ hh (by fun_prop)]
    exact hm _ (by nlinarith)
  have r := hA Ω _ (P.withDensity h) ν' U U' (t0 + 1) hU m' h01 (fun y => ⟨(p' y).1.le, (p' y).2⟩) (by omega)
    (fun j hj => (e j hj).trans (e' _).symm) fun j hj => by rw [e j hj]; exact ENNReal.ofReal_ne_top
  rw [withDensity_apply _ (measurableSet_lt measurable_const hU)] at r
  rw [r, show {y | 0 < U' y} = univ from eq_univ_of_forall fun y => (p' y).1]
  simpa using e' 0

theorem momW : MomW := momW_of momA momB

end PositivityTheory.RgFd
