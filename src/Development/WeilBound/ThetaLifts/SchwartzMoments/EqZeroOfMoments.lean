module

public import Development.WeilBound.ThetaLifts.SchwartzMoments.MulLPowApply
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.NormIteratedFDerivCexpCompLe
public import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.DictIrr
import Development.WeilBound.ThetaLifts.SchwartzMoments.DenseC
public import Development.WeilBound.ThetaLifts.SchwartzMoments.JetApply
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKOwn

open Filter Topology Complex PositivityTheory.ThKG.Loc.Bump
open scoped SchwartzMap ContDiff

theorem eq_zero_of_moments {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Q : X → ℂ} {w : ℝ} (hQ : Q.HasTemperateGrowth) (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2)
    {g : 𝓢(X, ℂ)} (hg : ∀ x, g x = cexp (Q x)) (T : 𝓢(X, ℂ) →L[ℂ] ℂ)
    (hT : ∀ (L : X →L[ℝ] ℝ) (m : ℕ), T ((mulL L ^ m) g) = 0) : T = 0 := by
  have hk := kill_mul weakInt T g fun L => kill_exp L hQ hw hre hg T (hT L) I fun x => by
    rw [SchwartzMap.smulLeftCLM_apply_apply (ex_temp L), smul_eq_mul, ex]
  refine ContinuousLinearMap.coeFn_injective (T.continuous.ext_on dense_compactSupport continuous_const fun φ hφ => ?_)
  have hs : HasCompactSupport fun x => φ x * cexp (-Q x) := HasCompactSupport.mul_right hφ
  have hm : ContDiff ℝ ∞ fun x => φ x * cexp (-Q x) := (φ.smooth ⊤).mul (Complex.contDiff_exp.comp hQ.1.neg)
  have e : φ = SchwartzMap.smulLeftCLM ℂ (hs.toSchwartzMap hm) g := by
    ext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.hasTemperateGrowth _), smul_eq_mul,
      HasCompactSupport.toSchwartzMap_toFun, hg]
    rw [mul_assoc, ← Complex.exp_add]
    simp
  change T φ = 0
  rw [e]
  exact hk _

def polE {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (y : EuclideanSpace ℝ (Fin n)) : ℂ :=
  MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) P

theorem eq_zero_PG {n : ℕ} (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : q.HasTemperateGrowth) (w : ℝ) (hw : 0 < w)
    (hlow : ∀ x, w * ‖x‖ ^ 2 ≤ q x) (T : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ)
    (hT : ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∃ P, ∀ y, f y = polE P y * cexp (-(q y : ℂ))) → T f = 0) : T = 0 := by
  have hQ : (fun y => -(q y : ℂ)).HasTemperateGrowth := (Complex.ofRealCLM.hasTemperateGrowth.comp hq).neg
  have hre : ∀ y, (-(q y : ℂ)).re ≤ -w * ‖y‖ ^ 2 := fun y => by
    rw [Complex.neg_re, Complex.ofReal_re]
    linarith [hlow y]
  refine eq_zero_of_moments hQ hw hre (g := GlobalTheory.CompanionTheory.OM.GaussSch.cexpSchwartz hQ hw hre) (fun _ => rfl) T fun L m =>
    hT _ ⟨(∑ i, MvPolynomial.C ((L (EuclideanSpace.single i 1) : ℝ) : ℂ) * MvPolynomial.X i) ^ m, fun y => ?_⟩
  have hL : L y = ∑ i, L (EuclideanSpace.single i 1) * y i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr y]

    simp [map_sum, mul_comm]
  rw [mulL_pow_apply, hL]

  simp only [polE, map_pow, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  push_cast
  rfl

end PositivityTheory.ThKOwn

end
