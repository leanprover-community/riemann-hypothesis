module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartImageNull
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ChartDimLtTorus
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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

open MvPolynomial Algebra

noncomputable section

theorem ChartDimLt.proof : ChartDimLt.Statement := by
  intro K _ ι _ J e p hJ hdim
  have key : ∀ Z ∈ (ReciprocityTheory.AnForm.R.chartIdeal J p).minimalPrimes,
      ∃ s : ℕ, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Z) = s ∧ s < e := by
    intro Z hZ
    have : Z.IsPrime := hZ.1.1
    obtain ⟨s, hs, hle⟩ := ChartDimLt.exists_dim_add_card_le hJ p Z hZ.1.2
    have hlt : ((s + Fintype.card K : ℕ) : WithBot ℕ∞) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      lt_of_le_of_lt hle hdim
    have hlt' : s + Fintype.card K < e + Fintype.card K := by exact_mod_cast hlt
    exact ⟨s, hs, by omega⟩
  cases e with
  | zero =>
    refine lt_of_le_of_lt
      (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ⊥) _ fun Z hZ => ?_)
      (WithBot.bot_lt_coe _)
    obtain ⟨s, -, hs⟩ := key Z hZ
    omega
  | succ n =>
    have hn : ((n : ℕ) : WithBot ℕ∞) < ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
    refine lt_of_le_of_lt
      (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ((n : ℕ) : WithBot ℕ∞)) _
        fun Z hZ => ?_) hn
    obtain ⟨s, hs, hsn⟩ := key Z hZ
    rw [hs]
    exact_mod_cast (by omega : s ≤ n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
