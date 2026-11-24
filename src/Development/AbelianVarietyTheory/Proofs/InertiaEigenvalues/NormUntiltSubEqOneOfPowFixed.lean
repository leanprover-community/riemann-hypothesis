module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.TiltAbs

theorem norm_untilt_sub_eq_one_of_pow_fixed :
    ∀ (l : ℕ) [Fact l.Prime] (o : ℕ) (ζ ζ' : Formalism.Per.Fl l), 0 < o → ζ ^ (l ^ o) = ζ →
      ζ' ^ (l ^ o) = ζ' → ζ ≠ ζ' → ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 := by
  intro l _ o ζ ζ' ho h1 h2 hne
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  set d : Formalism.Per.Fl l := ζ - ζ' with hd
  have hdpow : d ^ (l ^ o) = d := by
    rw [hd, sub_pow_char_pow, h1, h2]
  have hd0 : d ≠ 0 := sub_ne_zero.2 hne
  set a : ℝ := ‖((d.untilt : Formalism.Per.OC l) : ℂ_[l])‖ with ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hd0
    refine (untilt_ultrametric_definite l d 0).2 ?_
    have : ((d.untilt : Formalism.Per.OC l) : ℂ_[l]) = 0 := norm_eq_zero.1 h
    exact Subtype.ext this
  have hapow : a ^ (l ^ o) = a := by
    have := congrArg (fun x : Formalism.Per.Fl l => ‖((x.untilt : Formalism.Per.OC l) : ℂ_[l])‖) hdpow
    simp only [map_pow, SubmonoidClass.coe_pow, norm_pow] at this
    exact this
  have hlo : 1 ≤ l ^ o := Nat.one_le_pow _ _ (by omega)
  have hlo' : l ^ o - 1 ≠ 0 := by
    have : 1 < l ^ o := Nat.one_lt_pow (by omega) hl
    omega
  have hsub : a ^ (l ^ o - 1) = 1 := by
    have : a ^ (l ^ o - 1) * a = 1 * a := by
      rw [← pow_succ, Nat.sub_add_cancel hlo, hapow, one_mul]
    exact mul_right_cancel₀ ha0 this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hlo').1 hsub

end GlobalTheory.TiltAbs
