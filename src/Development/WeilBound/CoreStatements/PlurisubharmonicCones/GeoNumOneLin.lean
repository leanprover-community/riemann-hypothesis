module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace LevelTowerAlt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem geoNum_one_lin (W : Ideal (MRing J)) :
    ∃ d : K → ℤ, (∀ k, 0 ≤ d k) ∧ ∀ a : K → ℤ, geoNum 1 W (fun _ => a) = ∑ k, a k * d k := by
  classical
  obtain ⟨g0, hg0⟩ : ∃ g0 : Ideal (MRing J) → ℤ, ∀ V b, geoNum 0 V b = g0 V :=
    ⟨fun V => geoNum 0 V (fun i => Fin.elim0 i), fun V b => congrArg _ (Subsingleton.elim _ _)⟩
  have hnn : ∀ V, 0 ≤ g0 V := by
    intro V
    rw [← hg0 V (fun i => Fin.elim0 i)]
    exact dite_nonneg (fun _ => Int.natCast_nonneg _) (fun _ => le_rfl)
  by_cases hW : IsRelevant W
  · refine ⟨fun k => ∑ᶠ V ∈ divSupp W (X ⟨k, (hW k).choose⟩ : MRing J),
        (multAt (W ⊔ Ideal.span {(X ⟨k, (hW k).choose⟩ : MRing J)}) V : ℤ) * g0 V, ?_, ?_⟩
    · intro k
      exact finsum_nonneg fun V => finsum_nonneg fun _ => mul_nonneg (Int.natCast_nonneg _) (hnn V)
    · intro a
      change (if h : IsRelevant W then
          ∑ k, a k * ∑ᶠ V ∈ divSupp W (X ⟨k, (h k).choose⟩ : MRing J),
            (multAt (W ⊔ Ideal.span {(X ⟨k, (h k).choose⟩ : MRing J)}) V : ℤ) *
              geoNum 0 V (Fin.init fun _ : Fin 1 => a)
        else 0) = _
      rw [dite_eq_left hW]
      simp only [hg0]
  · refine ⟨fun _ => 0, fun _ => le_rfl, fun a => (dif_neg hW).trans ?_⟩
    simp

end LevelTowerAlt
