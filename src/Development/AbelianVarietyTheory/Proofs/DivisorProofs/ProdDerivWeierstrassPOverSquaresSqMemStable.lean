module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntermediateFieldOfForallComplexAutFixedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZeroStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.sqProd_sq_mem_and_stable : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t →
    sqProd p L t ^ 2 ∈ F ∧ (sqProd p L t ∈ F → Stable L F (sqPt p t)) := by
  intro p F L t hp h4 h3 hD
  refine ⟨?_, ?_⟩
  · apply GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F
    intro σ hσ
    rw [map_pow]
    rcases GlobalTheory.T.prodDerivWeierstrassPOverSquares_conj p F L t hp h4 h3 hD σ hσ with ⟨h, _⟩ | h
    · rw [h]
    · rw [h, neg_sq]
  · intro hmem σ hσ
    rcases GlobalTheory.T.prodDerivWeierstrassPOverSquares_conj p F L t hp h4 h3 hD σ hσ with ⟨_, he⟩ | h
    · exact he
    · exfalso
      have hne := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp h4 h3 hD).2
      have hfix : σ (sqProd p L t) = sqProd p L t := hσ _ hmem
      rw [hfix] at h
      have h2 : (2 : ℂ) * sqProd p L t = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2 with h2 | h2
      · norm_num at h2
      · exact hne h2
