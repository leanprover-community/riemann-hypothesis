module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LowestKTypeLink
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LowestKTypeVectorExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.MemEigenTensorSpaceIff
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolPowerDetDiag
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SACommSES
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.IndicatorRholMem

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem k2V (n : ℕ) : EigenspaceWeightConeStandard n := by
  intro ε lam h H _ _ _ σ D E V s hσ hD hV hc hVK hint hanti hgap hp hq
  obtain ⟨T, μ, ι, hμ, hιK, hcoef⟩ := k2vLink n ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq
  obtain ⟨hEM, hlow, hwt, hgen⟩ := k2vM lam μ hμ
  have hVst := hV.2.1
  have : FiniteDimensional ℂ V := hV.1
  have hw0 := lowestKType_vector_exists ε lam σ D E V hσ hD hV T ι hιK
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hU' : ∀ a b, ε a = ε b → ∀ x y : D, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ := by
    intro a b hab x y
    rw [hU a b x y, adjSign, if_pos hab, one_mul]
  have hℓ : ∀ (a : Fin n) (v w : V), (w : D) = E a a v →
      submoduleEvaluationFunctional V (ι.symm T.w) w = ((lowK ε lam a : ℝ) : ℂ) * submoduleEvaluationFunctional V (ι.symm T.w) v := by
    intro a v w hw
    change ⟪((ι.symm T.w : V) : D), (w : D)⟫_ℂ =
      ((lowK ε lam a : ℝ) : ℂ) * ⟪((ι.symm T.w : V) : D), (v : D)⟫_ℂ
    rw [hw, ← hU' a a rfl, hw0.1 a, inner_smul_left, Complex.conj_ofReal]
  refine lowestKType_tensor_lift ε lam s hanti E (genSub E V) (eMM μ) (phiMM μ) hEM hlow hwt hgen (sT E V)
    (sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w))) (sES V) (sA ε E V hVst)
    (_root_.ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sA_isKRel ε E V hVst hD.glRep) (sT_sES E V) (sθ_sES V _ _ _)
    (fun a b hab => _root_.ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sA_comm_sES ε E V hVst a b hab) ?_ ?_ ?_
  · intro a x
    exact _root_.ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sθ_sA ε E V hVst (eMM μ) hEM (phiMM μ) (lam + rho n) (lowK ε lam) hwt (submoduleEvaluationFunctional V (ι.symm T.w)) hℓ a x
  · intro W hW hθ
    exact lowestKType_trace ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq T μ ι hμ hιK hcoef W hW hθ
  · intro μ' f hf hk
    exact lift_highestWeightVector ε E V hVst hD.glRep hU' μ' f hf hk

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
