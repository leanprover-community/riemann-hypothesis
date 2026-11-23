module

public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.HlamStable
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamKTypeBounds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdCons
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem gapNorm_of (hD : DegPsi) : GapNorm := by
  intro n ε hp hq
  refine ⟨G2.thrS ε + 2, fun lam hlam hgap T μ hμ => ?_⟩
  have hh : G2.thrS ε + 1 < G2.thrS ε + 2 := by linarith
  have hq0 := G2.one_le_q0_of_p_q_pos hp hq
  have h8 := G2.fdc_eight hh
  have hP : IsPsiFor ε lam T (PsiM T μ) := (S7.isPsiFor_psiM ε lam _ T μ hlam hμ hgap hq0 h8).1
  have hgap' := G2.fdc_stdGap hlam hgap hh
  have hw := G2.fdc_w_ne T
  have hDS := G2.isDS_sigLam hgap' hP hw
  have : CompleteSpace (Hlam ε (PsiM T μ) T.w) := hDS.1
  have : Nontrivial (Hlam ε (PsiM T μ) T.w) := hDS.2.1
  obtain ⟨d, hd⟩ := G2.fdcGood_of_isDS hDS
  obtain ⟨x, hx⟩ := exists_ne (0 : Hlam ε (PsiM T μ) T.w)
  have hΨ : ∀ μ' : Fin n → ℝ, IsHCParam μ' → GapAtLeast ε μ' (G2.thrS ε + 2) →
      ∃ (T' : KType ε (lowK ε μ')) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)), IsPsiFor ε μ' T' Ψ := by
    intro μ' hμ' hg'
    obtain ⟨T'⟩ := HW.kType_exists ε μ' hμ'
    obtain ⟨m', -, hP'⟩ := G2.fdc_model hp hq hμ' hg' hh T'
    exact ⟨T', _, hP'⟩
  have hdeg := G2.fdCons_cd hp hq hlam hgap hh hΨ hDS hx
  rw [fdegOf_of_isFdeg' hd hx] at hdeg
  subst hdeg
  set C : ℝ := ‖uniformisationL2 ε (PsiM T μ) T.w T.w‖ ^ 2 with hC
  have hC0 : 0 < C := by
    have := G2.datumEmbedding_highest_ne_zero hgap' hP hw
    positivity
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := umat_mem_UJset ε 1
  refine hD n ε T.V (PsiM T μ) (Hlam ε (PsiM T μ) T.w) (sigLam ε (PsiM T μ) T.w)
    (fun v => ⟨uniformisationL2 ε (PsiM T μ) T.w v, datumEmbedding_mem_Hlam hP v⟩) C (dimVlam lam) (muCD ε) hC0 (fun v v' => ?_) (fun g v v' => ?_) hd
  · have e := G2.formulaF_sigLam hgap' hP hw h1 v v'
    rw [hP.2.1] at e
    simp only [ContinuousLinearMap.one_apply] at e
    rw [← e, (G2.sigLam_isURepOn hgap' hP hw).1.1]
    rfl
  · exact G2.formulaF_sigLam hgap' hP hw (umat_mem_UJset ε g) v v'

end CompanionTheory.RgFd
