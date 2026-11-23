module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimBdPfKFin
public import Formalism.HermitianCurvature.StatementM
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero

@[expose] public section

noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.D.Upq.Coef

section UJ

open ReciprocityTheory.ChartRestriction.DS

theorem fdeg_gap (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (h : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      120 * (n : ℝ) ^ 3 ≤ h → 1 ≤ pOf ε → 1 ≤ qOf ε → v ≠ 0 →
      Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam := by
  obtain ⟨c, hc, hH⟩ := fdCons_muG n ε
  refine ⟨c, hc, fun lam h H _ _ _ σ v hl hσ hgap hh hp hq hv => ?_⟩
  have hn : 1 ≤ n := hp.trans ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
  have ht : thrStar ε ≤ 32 * (n : ℝ) ^ 3 := by
    have hp_le : pOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    have hq_le : qOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    have hq0_le : S7.q0 ε ≤ n := (min_le_right _ _).trans hq_le
    have hp_real : (pOf ε : ℝ) ≤ n := by exact_mod_cast hp_le
    have hq_real : (qOf ε : ℝ) ≤ n := by exact_mod_cast hq_le
    have hq0_real : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast hq0_le
    have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn_le_cube : (n : ℝ) ≤ (n : ℝ) ^ 3 := le_self_pow₀ hn_real (by norm_num)
    have hsq_le_cube : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 :=
      pow_le_pow_right₀ hn_real (by norm_num)
    unfold thrStar
    apply max_le
    · have hprod : (n : ℝ) * pOf ε * qOf ε ≤ n * n * n := by gcongr
      nlinarith
    · have hsqrt : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n :=
        Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
      have hprod : 16 * (n : ℝ) * S7.q0 ε ≤ 16 * n * n := by gcongr
      nlinarith
  refine hH lam H σ v hl hσ h hgap (by linarith) hp hq (fun μ hμ hg => ?_) hv
  have hq0 : 1 ≤ S7.q0 ε := by unfold S7.q0; omega
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε :=
      le_max_right _ _
    have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    linarith
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor S7.psiExists T hμ hg hq0 h8
  exact ⟨T, Ψ, hP⟩

end UJ


open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] [CompleteSpace Wp] [CompleteSpace Wq]

end CompanionTheory.D.Upq.Coef

end
