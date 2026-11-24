module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LowerBoundOfBaseSetting
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.HH

theorem exists_word {J : Type} : ∀ (d : ℕ) (m : J →₀ ℕ), m.degree = d →
    ∃ w : Fin d → J, m = ∑ k, Finsupp.single (w k) 1 := by
  intro d
  induction d with
  | zero =>
    intro m hm
    refine ⟨Fin.elim0, ?_⟩
    rw [(Finsupp.degree_eq_zero_iff m).1 hm]
    simp
  | succ d ih =>
    intro m hm
    have hne : m ≠ 0 := by
      rintro rfl
      simp at hm
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hne
    have hle : Finsupp.single j 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hj
      omega
    have hsplit : m = Finsupp.single j 1 + (m - Finsupp.single j 1) :=
      (add_tsub_cancel_of_le hle).symm
    have hdeg : Finsupp.degree (m - Finsupp.single j 1) = d := by
      have h2 := congrArg Finsupp.degree hsplit
      rw [map_add (f := _), Finsupp.degree_single, hm] at h2
      omega
    obtain ⟨w', hw'⟩ := ih _ hdeg
    refine ⟨Fin.cons j w', ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hw']
    exact hsplit

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem hhFl_word (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    (hP : IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1))
    (w : Fin (dimFl Ψ N + 1) → Ψ × Fin N) (c : ℝ) :
    hhFl Ψ N II (monomial (∑ k, Finsupp.single (w k) 1) c) = c * ((-1) ^ (dimFl Ψ N + 1) *
      II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
        (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w k))) := by
  have hdeg : (∑ i, Finsupp.single (w i) (1 : ℕ)).degree = dimFl Ψ N + 1 := by

    rw [map_sum]
    simp [Finsupp.degree_single]
  rw [HhModel.hhFl_monomial, hdeg]
  congr 2
  exact GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.hFlMono_sum_single Ψ N II hII hP w

end RootFieldNumerics.HH
