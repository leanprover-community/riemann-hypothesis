module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontalMult
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialLocalizedLength
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

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem BlowUpHorizontalMult.proof (hmin : BlowUpHorizontalMinimal.Statement.{u})
    (hchart : BlowUpHorizontalChartLength.Statement.{u}) : BlowUpHorizontalMult.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  have hm := hmin O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW
  obtain ⟨hWp, hBW, hrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  obtain ⟨-, -, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hrel
  have hcond : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    unfold divCycle at hW
    rw [dite_eq_right h] at hW
    exact hW rfl
  have hch := hchart O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP W hW hϖW hWp
  have := hWp
  have hp := PolynomialLocalizedLength.full (MRing ι O) (W.comap (liftForm (ι := ι) (J := J) (R := O))) (P ⊔ Ideal.span {x})
  unfold divCycle
  rw [dite_eq_left ⟨hm, hrel₀⟩, dite_eq_left hcond]
  congr 2
  exact (hp.symm.trans hch.symm : _)

end GroundTheory.Heights₂.Heights.NumbersDVR
