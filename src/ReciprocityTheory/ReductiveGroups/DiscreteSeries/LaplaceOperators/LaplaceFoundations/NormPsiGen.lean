module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.ContinuousSecondMatrix
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS Formalism.QuantumDeterminants

variable {k r : ℕ}

theorem inUJ_kmul {ε : Fin (2 * r + k + 1) → Bool} {κ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hκ : κ ∈ Kset ε) : inUJ ε (κ * g) ↔ inUJ ε g := by
  have hJ : κᴴ * Jm ε * κ = Jm ε := HW.torep_inUJ ε hκ
  unfold inUJ
  rw [Matrix.conjTranspose_mul]
  have e : gᴴ * κᴴ * Jm ε * (κ * g) = gᴴ * (κᴴ * Jm ε * κ) * g := by simp only [Matrix.mul_assoc]
  rw [e, hJ]

theorem psiM_zero {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : ¬ inUJ ε g) :
    S7.PsiM T μ g = 0 := by
  unfold S7.PsiM
  rw [dite_eq_right]
  rintro ⟨k', X, hX, rfl⟩
  exact hg (S7.inUJ_kexp k' hX)

theorem psiM_K {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) {κ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hκ : κ ∈ Kset ε)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    S7.PsiM T μ (κ * g) = HW.torepSig T κ * S7.PsiM T μ g := by
  by_cases hg : inUJ ε g
  · have h := S7.psiM_equiv T μ (HW.torepK ε hκ) 1 hg
    rw [HW.toMK_torepK] at h
    have h1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
    rw [h1, Matrix.mul_one] at h
    rw [h, HW.torepSig_of_mem T hκ]
    have : T.op 1 = 1 := by simp [S7.KType.op]
    rw [this, mul_one]
  · rw [psiM_zero T μ hg, psiM_zero T μ (fun h => hg ((inUJ_kmul hκ).1 h)), mul_zero]

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) : Continuous (Formalism.MainNotions.S.psiGen k r z c) := by
  apply ReciprocityTheory.ChartRestriction.DS.Lap.CurveContinuity.psiGen_cont <;> assumption

theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ‖Formalism.MainNotions.S.psiGen k r z c g‖ = 1 := by
  unfold Formalism.MainNotions.S.psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem coef_meas {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) (hcont : ContinuousOn (S7.PsiM T μ) (UJset ε)) (v w : T.V) :
    Measurable (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) := by
  classical
  set s : Set (Mt k r) := {M | inUJ ε (Matrix.of M)}
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have hs : IsClosed s :=
    isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const
  have hΦ : ContinuousOn (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) s := by
    have h1 : ContinuousOn (fun M : Mt k r => S7.PsiM T μ (Matrix.of M)) s :=
      hcont.comp hc.continuousOn (fun M hM => hM)
    exact continuousOn_const.inner (h1.clm_apply continuousOn_const)
  have he : (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) =
      s.piecewise (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) (fun _ => 0) := by
    funext M
    by_cases hM : M ∈ s
    · rw [Set.piecewise_eq_of_mem _ _ _ hM]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hM, psiM_zero T μ hM]; simp
  rw [he]
  exact hΦ.measurable_piecewise continuousOn_const hs.measurableSet

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
