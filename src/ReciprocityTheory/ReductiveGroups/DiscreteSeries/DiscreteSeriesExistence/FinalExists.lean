module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Compact
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

theorem final_existsG_of (hS7 : ∀ m : ℕ, S7.PsiExistsStatement m) :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
          (16 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) +
            8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))) < h →
        ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
          (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ := by
  intro n ε lam hlam h hh hmax
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  by_cases hpq : pOf ε = 0 ∨ qOf ε = 0
  · obtain ⟨σ, hDS, -⟩ := isDS_compact hpq hlam T
    exact ⟨T.V, inferInstance, inferInstance, σ, hDS⟩
  · simp only [not_or] at hpq
    have hq : 1 ≤ S7.q0 ε := by
      show 1 ≤ min (pOf ε) (qOf ε)
      omega
    have hgap : StdGap ε lam := ⟨hlam.1, h, hh, (le_max_left _ _).trans_lt hmax⟩
    have h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
      have h16 := (le_max_right _ _).trans_lt hmax
      have hs : 0 ≤ Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ)) := Real.sqrt_nonneg _
      have hnq : 0 ≤ (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) := by positivity
      show 8 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) < h
      nlinarith
    obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor (hS7 n) T hlam hh hq h8
    exact ⟨_, inferInstance, inferInstance, sigLam ε Ψ T.w, isDS_sigLam hgap hP (HW.KType.w_ne_zero T)⟩

end ReciprocityTheory.ChartRestriction.DS
