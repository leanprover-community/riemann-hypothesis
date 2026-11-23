module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InConeRefl
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.ExplicitFunctionSquareIntegrable
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.DiscreteSeriesSU.GapInv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

@[expose] public section

noncomputable section

namespace CompanionTheory.RgDs

open ReciprocityTheory.ChartRestriction.DS

theorem model_of (hL : ExplicitFunctionSquareIntegrable) (hK : Key) (hH : Hilb) {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ ∧
        ∀ (η : Fin n → ℝ) (S : Submodule ℂ H), Formalism.MainNotions.S.IsKTypeOf ε σ η S → InCone (lowK ε lam) η := by
  obtain ⟨T⟩ := HW.kType_exists ε lam hl
  obtain ⟨μ, hμ⟩ := S7.exists_mu hl
  have hP : IsPsiFor ε lam T (S7.PsiM T μ) :=
    ⟨fun k₁ k₂ g hg => S7.psiM_equiv T μ k₁ k₂ hg, S7.psiM_one T μ, S7.psiM_smooth T μ hμ,
      fun g hg => S7.psiM_casimir T μ hμ hg, hL n ε lam T μ hl hμ⟩
  exact ⟨_, inferInstance, inferInstance, _, hH n ε lam T _ hl hP (hK n ε lam T μ hl hμ hP)⟩

theorem dsExists_of (hL : ExplicitFunctionSquareIntegrable) (hK : Key) (hH : Hilb) : GlobalTheory.Dec.DSExists := by
  intro n ε lam hl
  obtain ⟨H, _, _, σ, h, -⟩ := model_of hL hK hH ε lam hl
  exact ⟨H, _, _, σ, h⟩

theorem kTypesAbove_of (hL : ExplicitFunctionSquareIntegrable) (hK : Key) (hH : Hilb) : GlobalTheory.Dec.KTypesAbove := by
  intro n ε lam H _ _ σ hl hσ μ S hS
  obtain ⟨G, _, _, π, hπ, hc⟩ := model_of hL hK hH ε lam hl
  obtain ⟨S', hS'⟩ := GlobalTheory.LowestKTypeDetermines.exists_ktype_of_uEquiv
    (CompanionTheory.DiscreteSeriesGap.GapInv.dsUnique_dec n ε lam H σ G π hl hσ hπ) ⟨S, hS⟩
  exact hc μ S' hS'

end CompanionTheory.RgDs
