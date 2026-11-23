module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceBranchExists
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceOnComponent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimePlaceBranchExists
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

open MvPolynomial ComplexSets

theorem PlaceBranchExists.proof (h₁ : PlaceOnComponent.Statement) (h₂ : PrimePlaceBranchExists.Statement) :
    PlaceBranchExists.Statement := by
  intro n I q hrad hdim P
  obtain ⟨J, hJ, -, hdimJ, P', hP'⟩ := h₁ n I q hrad hdim P
  obtain ⟨ν, hν⟩ := h₂ n J q hJ.1.1 hdimJ P'

  let ν' : VarBranch I 1 q :=
    { radius := ν.radius, radius_pos := ν.radius_pos, toFun := ν.toFun, differentiableOn := ν.differentiableOn,
      injOn := ν.injOn, map_zero := ν.map_zero,
      mapsTo := fun t ht g hg ↦ ν.mapsTo ht g (hJ.1.2 hg) }
  have hord : ∀ f, branchOrder ν' f = branchOrder ν f := fun _ ↦ rfl
  exact ⟨ν', fun f ↦ (hP' f).trans ((hν f).trans (hord f).symm)⟩

end GroundTheory.Heights₂.Heights
