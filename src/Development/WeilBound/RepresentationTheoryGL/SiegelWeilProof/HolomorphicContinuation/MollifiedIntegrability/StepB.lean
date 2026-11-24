module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.MollId
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]


theorem step_b (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t ε : ℝ) (hε : 0 < ε)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (C : ℂ) :
    ∫ β, ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ)) =
      ∫ x, Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) ∂μ := by
  have hm : Measurable (fun p : E n × X => kr ε t (qq p.2 - p.1)) :=
    (continuous_kr ε t hε).measurable.comp ((hqq.comp measurable_snd).sub measurable_fst)
  have hs : AEStronglyMeasurable (fun p : E n × X => Ψ p.2) ((volume : Measure (E n)).prod μ) :=
    hΨ.aestronglyMeasurable.comp_snd
  have hψm : AEStronglyMeasurable (fun p : E n × X => ψ p.1) ((volume : Measure (E n)).prod μ) :=
    (hψc.measurable.comp measurable_fst).aestronglyMeasurable
  have hint : Integrable (fun p : E n × X => ψ p.1 * (C * (Ψ p.2 * kr ε t (qq p.2 - p.1))))
      ((volume : Measure (E n)).prod μ) := by
    refine Integrable.mono' ((hψi.norm.mul_prod hΨ.norm).mul_const (‖C‖ * ∫ y, ‖gam (n := n) ε y‖))
      (hψm.mul (aestronglyMeasurable_const.mul (hs.mul hm.aestronglyMeasurable))) ?_
    refine Eventually.of_forall fun p => ?_
    obtain ⟨β, x⟩ := p
    show ‖ψ β * (C * (Ψ x * kr ε t (qq x - β)))‖ ≤ ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖)
    rw [norm_mul, norm_mul, norm_mul]
    have hk := norm_kr_le ε t hε (qq x - β)
    calc ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ‖kr ε t (qq x - β)‖)) ≤
          ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ∫ y, ‖gam (n := n) ε y‖)) := by gcongr
      _ = ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖) := by ring
  have e1 : (fun β : E n => ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ))) =
      fun β => ∫ x, ψ β * (C * (Ψ x * kr ε t (qq x - β))) ∂μ := by
    funext β
    rw [← integral_const_mul, ← integral_const_mul]
  have e2 : (fun x : X => ∫ β : E n, ψ β * (C * (Ψ x * kr ε t (qq x - β)))) =
      fun x => Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) := by
    funext x
    rw [← integral_const_mul]
    congr 1
    funext β
    ring
  rw [e1, integral_integral_swap (f := fun (β : E n) (x : X) => ψ β * (C * (Ψ x * kr ε t (qq x - β)))) hint, e2]

end PositivityTheory.Rg.Sw.WR.D.Moll
