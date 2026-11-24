module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionsGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjHomInjective
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsOpen
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsExists
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

theorem FiniteProjectionsContainOpen.proof (h₁ : ConeAvoidsFinite.Statement)
    (h₂ : FiniteProjHomInjective.Statement) (h₃ : ConeAvoidsOpen.Statement)
    (h₄ : ConeAvoidsExists.Statement) : FiniteProjectionsContainOpen.Statement := by
  intro n d J hJ hd
  obtain ⟨A₀, N, hA₀⟩ := h₄ n d J hJ hd
  refine ⟨{A | ConeAvoids J A N}, h₃ n d N J, ⟨A₀, hA₀⟩, fun A hA => ?_⟩
  have hfin : (projHom J A).toRingHom.Finite := h₁ n d N J A hA
  exact ⟨h₂ n d J A hJ hd hfin, hfin⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
