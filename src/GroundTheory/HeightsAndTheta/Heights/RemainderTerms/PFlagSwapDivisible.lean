module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem FlagSwapDivisible.dvd_sub_substitute {R σ : Type} [CommRing R] [DecidableEq σ] (a b : σ)
    (Q : MvPolynomial σ R) :
    (X a - X b : MvPolynomial σ R) ∣
      Q - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p k hp =>
    rw [map_mul, aeval_X]
    have hk : (X a - X b : MvPolynomial σ R) ∣
        X k - (if k = a then (X b : MvPolynomial σ R) else X k) := by
      split_ifs with h
      · subst h; exact dvd_rfl
      · simp
    have e : p * X k - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
          (if k = a then (X b : MvPolynomial σ R) else X k) =
        (p - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p) * X k +
          aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
            (X k - (if k = a then (X b : MvPolynomial σ R) else X k)) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hk _)

theorem FlagSwapDivisible.proof : FlagSwapDivisible.Statement := by
  intro σ _ P a b hab hP
  set g : σ → MvPolynomial σ ℚ := fun v => if v = a then X b else X v with hg
  have hswap : g ∘ Equiv.swap a b = g := by
    funext v
    simp only [Function.comp_apply, hg]
    rcases eq_or_ne v a with rfl | hva
    · simp [Equiv.swap_apply_left, hab.symm]
    · rcases eq_or_ne v b with rfl | hvb
      · simp [Equiv.swap_apply_right, hva]
      · simp [Equiv.swap_apply_of_ne_of_ne hva hvb, hva]
  have hzero : aeval g P = 0 := by
    have h1 : aeval g P = -aeval g P := by
      calc aeval g P = aeval (g ∘ Equiv.swap a b) P := by rw [hswap]
        _ = aeval g (rename (Equiv.swap a b) P) := (aeval_rename _ _ _).symm
        _ = -aeval g P := by rw [hP, map_neg]
    have h2 : aeval g P + aeval g P = 0 := by
      nth_rewrite 2 [h1]; exact add_neg_cancel _
    have h3 : (2 : MvPolynomial σ ℚ) * aeval g P = 0 := by rw [two_mul]; exact h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hd := FlagSwapDivisible.dvd_sub_substitute a b P
  rw [← hg, hzero, sub_zero] at hd
  exact hd

end

end RestTerms

end GroundTheory.Heights₂.Heights
