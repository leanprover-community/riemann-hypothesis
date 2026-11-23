module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMLocusOpen
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMProjDimCriterion
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjDimSpread
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIdealHeightSpread
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GroundTheory.Heights₂.Heights

theorem CMLocusOpen.proof (hcrit : CMProjDimCriterion.Statement) (hpd : ProjDimSpread.Statement)
    (hht : IdealHeightSpread.Statement) : CMLocusOpen.Statement := by
  intro n I P _ hIP hCM
  obtain ⟨ℓ, hℓ, hℓht⟩ := (hcrit n I P hIP).mp hCM
  obtain ⟨g₁, hg₁P, hg₁⟩ := hpd (MvPolynomial (Fin n) ℂ) I P ℓ hℓ
  obtain ⟨g₂, hg₂P, hg₂⟩ := hht (MvPolynomial (Fin n) ℂ) I P hIP
  refine ⟨g₁ * g₂, fun h => (‹P.IsPrime›.mem_or_mem h).elim hg₁P hg₂P, fun Q _ hIQ hgQ => ?_⟩
  have h₁ : g₁ ∉ Q := fun h => hgQ (Q.mul_mem_right g₂ h)
  have h₂ : g₂ ∉ Q := fun h => hgQ (Q.mul_mem_left g₁ h)
  exact (hcrit n I Q hIQ).mpr ⟨ℓ, hg₁ Q h₁, hℓht.trans (hg₂ Q hIQ h₂)⟩

end GroundTheory.Heights₂.Heights
