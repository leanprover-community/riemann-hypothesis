module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsWord
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics

theorem HH.sum_xDeg {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (τ : Ψ) :
    ∑ i : Fin N, GroundTheory.Heights₂.Heights.LowerBoundFree.xDeg Ψ N (τ, i) = 0 := by
  funext q
  obtain ⟨σ, a⟩ := q
  rw [Finset.sum_apply, Pi.zero_apply]
  have ha : (a:ℕ) + 1 < N := by have := a.isLt; omega
  by_cases h : σ = τ
  · subst h
    simp only [GroundTheory.Heights₂.Heights.LowerBoundFree.xDeg, if_true]
    rw [Finset.sum_sub_distrib]
    rw [Fin.sum_univ_eq_sum_range (fun n => if (a:ℕ) = n then (1:ℤ) else 0) N,
        Fin.sum_univ_eq_sum_range (fun n => if (a:ℕ) + 1 = n then (1:ℤ) else 0) N]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega)),
        if_pos (Finset.mem_range.mpr ha)]
    simp
  · simp [GroundTheory.Heights₂.Heights.LowerBoundFree.xDeg, h]

open GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear in
theorem flag_height_power_sum_zero : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (Q : RP Ψ N), 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) → Q.IsHomogeneous (dimFl Ψ N) → hhFl Ψ N II (pk τ 1 * Q) = 0 := by
  intro II hII Ψ _ _ N τ Q hN hP hQ
  have key : ∀ (w : Fin (dimFl Ψ N) → Ψ × Fin N),
      ∑ i : Fin N, II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N)
        (dimFl Ψ N + 1)
        (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N
          (Fin.snoc (α := fun _ => Ψ × Fin N) w (τ, i) k)) = 0 := by
    intro w
    let f := GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.fsMultilin
      (hII.1 (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)) hP
    let u : Fin (dimFl Ψ N + 1) → GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N → ℤ :=
      Fin.snoc (α := fun _ => GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N → ℤ)
        (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xDeg Ψ N (w k)) 0
    have h1 : ∀ i : Fin N, II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N)
        (dimFl Ψ N + 1)
        (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N
          (Fin.snoc (α := fun _ => Ψ × Fin N) w (τ, i) k)) =
        f.toLinearMap u (Fin.last _) (GroundTheory.Heights₂.Heights.LowerBoundFree.xDeg Ψ N (τ, i)) := by
      intro i
      rw [MultilinearMap.toLinearMap_apply,
        GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.fsMultilin_apply]
      congr 1
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simp [u, GroundTheory.Heights₂.Heights.LowerBoundFree.xLine]
      · simp [u, GroundTheory.Heights₂.Heights.LowerBoundFree.xLine]

    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← map_sum, HH.sum_xDeg (N := N) τ, map_zero]

  rw [MvPolynomial.as_sum Q, Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  have hdeg : Finsupp.degree m = dimFl Ψ N := by
    have := hQ (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  obtain ⟨w, hw⟩ := HH.exists_word (dimFl Ψ N) m hdeg
  have hprod : pk τ 1 * monomial m (AddMonoidAlgebra.coeff Q m) =
      ∑ i : Fin N, monomial (∑ k : Fin (dimFl Ψ N + 1),
        Finsupp.single (Fin.snoc (α := fun _ => Ψ × Fin N) w (τ, i) k) 1) (AddMonoidAlgebra.coeff Q m) := by
    unfold pk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_one, X, monomial_mul, one_mul, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← hw, add_comm (Finsupp.single (τ, i) 1)]

  rw [hprod, map_sum,
  Finset.sum_congr rfl (fun i _ => HH.hhFl_word II hII.1 hP
    (Fin.snoc (α := fun _ => Ψ × Fin N) w (τ, i)) (AddMonoidAlgebra.coeff Q m)),
  ← Finset.mul_sum, ← Finset.mul_sum, key w, mul_zero, mul_zero]

end RootFieldNumerics
