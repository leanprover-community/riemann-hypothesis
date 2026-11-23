module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.MvPolynomial.Funext
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem exists_eval_ne_zero_of_isOpen {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0)
    {V : Set (Fin d → ℂ)} (hV : IsOpen V) (hne : V.Nonempty) : ∃ t ∈ V, eval t Q ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  obtain ⟨t, ht⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV t ht
  apply hQ
  refine MvPolynomial.funext_set (fun i => Metric.ball (t i) ε) (fun i => ?_) (fun x hx => ?_)
  · exact infinite_of_mem_nhds (t i) (Metric.ball_mem_nhds (t i) hε)
  · rw [map_zero]
    apply hall
    apply hball
    rw [ball_pi t hε]
    exact hx

theorem dense_eval_ne_zero {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0) :
    Dense {y : Fin d → ℂ | eval y Q ≠ 0} := by
  rw [dense_iff_inter_open]
  intro V hV hne
  obtain ⟨t, htV, ht⟩ := exists_eval_ne_zero_of_isOpen hQ hV hne
  exact ⟨t, htV, ht⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
