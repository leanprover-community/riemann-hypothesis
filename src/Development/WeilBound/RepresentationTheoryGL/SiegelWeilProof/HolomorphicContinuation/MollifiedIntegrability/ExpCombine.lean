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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem exp_combine (t : ℝ) (y q β : E n) :
    Complex.exp (Complex.I * t * ip y q) * Complex.exp (-(Complex.I * t * ip β y)) =
      Complex.exp (Complex.I * t * ip y (q - β)) := by
  rw [ip_sub_right, ip_comm β y, ← Complex.exp_add]
  congr 1
  push_cast
  ring


theorem step_a (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t ε : ℝ) (hε : 0 < ε)
    (β : E n) :
    ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
        Complex.exp (-(Complex.I * t * ip β y)) =
      ∫ x, Ψ x * kr ε t (qq x - β) ∂μ := by
  have hfun : ∀ (y : E n) (x : X), Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) =
      Ψ x * (gam ε y * Complex.exp (Complex.I * t * ip y (qq x - β))) := by
    intro y x
    rw [← exp_combine]
    ring
  have hL : ∀ y : E n, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) =
      ∫ x, Ψ x * (gam ε y * Complex.exp (Complex.I * t * ip y (qq x - β))) ∂μ := by
    intro y
    rw [← integral_mul_const, ← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun x => hfun y x)
  have hm1 : Measurable fun p : E n × X => ip p.1 (qq p.2 - β) :=
    continuous_ip.measurable.comp (measurable_fst.prodMk ((hqq.comp measurable_snd).sub_const β))
  have hm2 : Measurable fun p : E n × X => Complex.exp (Complex.I * t * ip p.1 (qq p.2 - β)) :=
    ((Complex.measurable_ofReal.comp hm1).const_mul (Complex.I * t)).cexp
  have hint : Integrable (fun p : E n × X =>
      Ψ p.2 * (gam ε p.1 * Complex.exp (Complex.I * t * ip p.1 (qq p.2 - β))))
      ((volume : Measure (E n)).prod μ) := by
    refine Integrable.mono ((integrable_gauss (n := n) ε hε).mul_prod hΨ) ?_ ?_
    · exact (hΨ.1.comp_snd (μ := (volume : Measure (E n)))).mul
        ((((continuous_gam ε).measurable.comp measurable_fst).mul hm2).aestronglyMeasurable)
    · refine Eventually.of_forall fun p => ?_
      simp only [norm_mul, norm_cexp_It, mul_one]
      exact le_of_eq (mul_comm _ _)
  simp only [hL, kr, ← integral_const_mul]
  exact integral_integral_swap hint

end PositivityTheory.Rg.Sw.WR.D.Moll
