module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterSumTopVanish
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StMixedTwistShift
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumAdditive
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

attribute [local instance] twistMonoid

theorem InterSumTopVanish.proof (hM : MixedTwistShift.Statement.{u, w}) : InterSumTopVanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L hW
  classical
  set L₀ : Fin n → LineBundle k x := fun j => L (Fin.castSucc j) with hL₀
  have hdim : ringKrullDim (Poly k N ⧸ pp) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := hW.dim.le
  have hA := hM k Ω N x n pp hW.isPrime hW.homog hW.le hdim L₀ (L (Fin.last n)) 0
  have hB := hM k Ω N x n pp hW.isPrime hW.homog hW.le hdim L₀ (twistBundle k x 0) 0
  filter_upwards [hA, hB] with c hAc hBc
  have hL : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
      (fun j => (L₀ j).toSubSystem) (L (Fin.last n)).toSubSystem := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hL₀]
  rw [interSum_eq_mixDiff, hL, mixDiff_snoc]
  have eA : mixDiff (fun g => restrLen pp (((L (Fin.last n)).toSubSystem * g).twist (twistSys k x (c : ℤ))))
      (fun j => (L₀ j).toSubSystem) =
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen pp (((tensorSub (fun i => (L₀ i).toSubSystem) T).twist (L (Fin.last n)).toSubSystem).twist
          (twistSys k x ((c : ℤ) + 0))) := by
    unfold mixDiff
    refine Finset.sum_congr rfl fun T _ => ?_
    have hc : (L (Fin.last n)).toSubSystem * ∏ j ∈ T, (L₀ j).toSubSystem =
        (∏ j ∈ T, (L₀ j).toSubSystem).twist (L (Fin.last n)).toSubSystem := SubSystem.twist_comm _ _
    rw [tensorSub_eq_prod, add_zero]
    beta_reduce
    rw [hc]
  have eB : mixDiff (fun F => restrLen pp (F.twist (twistSys k x (c : ℤ)))) (fun j => (L₀ j).toSubSystem) =
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen pp (((tensorSub (fun i => (L₀ i).toSubSystem) T).twist (twistBundle k x 0).toSubSystem).twist
          (twistSys k x ((c : ℤ) + 0))) := by
    unfold mixDiff
    refine Finset.sum_congr rfl fun T _ => ?_
    have hz : (∏ j ∈ T, (L₀ j).toSubSystem).twist (twistBundle k x 0).toSubSystem =
        ∏ j ∈ T, (L₀ j).toSubSystem := SubSystem.twist_twistSys_zero _
    rw [tensorSub_eq_prod, add_zero]
    beta_reduce
    rw [hz]
  rw [eA, eB, hAc, hBc, sub_self]

end

end GroundTheory.Heights₂.Heights.Kleiman
