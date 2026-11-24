module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.WeylBridge

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem hwfin_weyl {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    (Module.finrank ℂ T.V : ℝ) =
      (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
        ((Λ + rhoC ε) a - (Λ + rhoC ε) b)) /
      ((∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) *
        ∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ)) := by
  obtain ⟨σ, -, hU, hK⟩ := KType.exists_rep T
  have h := weyl_dimension_formula_product n ε Λ T.V σ ⊤ hU hK
  rw [finrank_top] at h
  exact h

theorem hwfin_denom (ε : Fin n → Bool) :
    (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b), (rhoC ε a - rhoC ε b)) =
      (∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) *
        ∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ) := by
  have h := hwfin_weyl (trivialKType ε)
  have h1 : (Module.finrank ℂ (trivialKType ε).V : ℝ) = 1 := by
    show (Module.finrank ℂ ℂ : ℝ) = 1
    simp
  rw [h1] at h
  simp only [zero_add] at h
  field_simp at h
  exact h.symm

theorem kType_finrank {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    (Module.finrank ℂ T.V : ℝ) = ∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
      ((Λ + rhoC ε) a - (Λ + rhoC ε) b) / (rhoC ε a - rhoC ε b) := by
  rw [hwfin_weyl T, ← hwfin_denom ε, ← Finset.prod_div_distrib]
  simp_rw [Finset.prod_div_distrib]

end ReciprocityTheory.ChartRestriction.DS.HW
