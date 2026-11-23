module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.BigMoment

theorem norm_dot_le_one {n : ℕ} {k : Type} [NormedField k] [IsUltrametricDist k] (c b : Fin n → k)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) : ‖c ⬝ᵥ b‖ ≤ 1 := by
  unfold dotProduct
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro i _
  rw [norm_mul]
  exact mul_le_one₀ (hc i) (norm_nonneg _) (hb i)

theorem dot_act {n : ℕ} {k : Type} [CommRing k] (g : GL (Fin n) k) (Y : Gl n k) :
    (act g Y).2.2.1 ⬝ᵥ (act g Y).2.1 = Y.2.2.1 ⬝ᵥ Y.2.1 := by
  simp only [act]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]

theorem dot_sec {r : ℕ} {k : Type} [CommRing k] (a : Inv (r + 1) k) :
    (sec a).2.2.1 ⬝ᵥ (sec a).2.1 = a.2.1 0 := by
  simp [sec, dotProduct, Fin.sum_univ_succ]

theorem dot_actU {n : ℕ} {E : Type} [CommRing E] [StarRing E] (g : Matrix.unitaryGroup (Fin n) E)
    (b : Fin n → E) : star (g.1 *ᵥ b) ⬝ᵥ (g.1 *ᵥ b) = star b ⬝ᵥ b := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp g.2, Matrix.one_mulVec]

theorem matchAt_unit_of_one_lt_norm :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (a : Inv (r + 1) F), 1 < ‖a.2.1 0‖ →
      MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  intro F E _ _ _ _ hU r M a ha
  haveI := hU.ultraF
  haveI := hU.ultraE
  have hG : orbG M (unitG (r + 1) F) (sec a) = 0 := by
    have h : ∀ g, unitG (r + 1) F (act g (sec a)) = 0 := by
      intro g
      unfold unitG
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨-, hb, hc, -⟩
      have := norm_dot_le_one _ _ hc hb
      rw [dot_act, dot_sec] at this
      exact absurd ha (not_lt.mpr this)
    simp [orbG, h]
  refine ⟨fun X hX => ?_, fun _ => hG⟩
  rw [hG]
  have h0 : star X.2.1 ⬝ᵥ X.2.1 = algebraMap F E (a.2.1 0) := by
    have := congrArg (fun t : Inv (r + 1) E => t.2.1 0) hX
    simpa [inv, mom, Hn.toGl, Inv.map] using this
  have h : ∀ g, unitU (r + 1) F E (actU g X) = 0 := by
    intro g
    unfold unitU
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨-, hb, -⟩
    have := norm_dot_le_one (star (actU g X).2.1) (actU g X).2.1
      (fun i => by rw [Pi.star_apply, hU.norm_star]; exact hb i) hb
    simp only [actU] at this
    rw [dot_actU, h0, norm_algebraMap'] at this
    exact absurd ha (not_lt.mpr this)
  simp [orbU, h]

end GlobalTheory.JR.BigMoment
