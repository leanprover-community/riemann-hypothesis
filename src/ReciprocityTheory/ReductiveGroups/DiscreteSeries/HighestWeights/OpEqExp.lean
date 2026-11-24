module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam
public import Formalism.RealPlaceAnalysis.Complexify

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem exists_log (ε : Fin n → Bool) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ toMK k = NormedSpace.exp Y := by
  have hk : toMK k ∈ Formalism.REAL.Kset ε := by
    rw [← Formalism.REAL.range_toMK]; exact ⟨k, rfl⟩
  obtain ⟨Y, hY, he, -⟩ := Formalism.REAL.kExp n ε (toMK k) hk
  exact ⟨Y, hY, he.symm⟩

theorem KType.op_eq_exp {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ T.op k = NormedSpace.exp (T.dτ Y) := by
  obtain ⟨Y, hY, he⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : γ 1 = k := onep_KG_ext (by rw [hγ, he]; simp)
  refine ⟨Y, hY, ?_⟩
  simpa [h1] using KType.op_curve T hY γ hγ 1

end ReciprocityTheory.ChartRestriction.DS.HW
