module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.HW

def HighestWeightExistsBody : Prop :=
  ∀ (k : ℕ) (u : Fin k → ℝ), Formalism.QuantumDeterminants.IsHCParam u →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsHCTypeU k u π

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem UJset_allPos_eq_Kset (k : ℕ) :
    Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) = Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k) := by
  have hJ : Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) = 1 := by
    unfold Formalism.REAL.Jm Formalism.MainNotions.S.allPos
    first
    | simp
  ext g
  first
  | simp only [Formalism.MainNotions.S.UJset, Formalism.REAL.Kset, Set.mem_setOf_eq, Formalism.REAL.inUJ, hJ, mul_one, one_mul,
      and_true, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]

theorem highest_weight_exists : HighestWeightExistsBody := by
  intro k u hu
  obtain ⟨T⟩ := kType_exists (Formalism.MainNotions.S.allPos k) u hu
  obtain ⟨σ, -, hU, hK⟩ := KType.exists_rep T
  refine ⟨T.V, inferInstance, inferInstance, σ, ?_, inferInstance, ?_, hK⟩
  · refine ⟨⟨T.w, 0, ?_⟩⟩
    intro h
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · rw [UJset_allPos_eq_Kset]
    exact hU

end ReciprocityTheory.ChartRestriction.DS.HW
