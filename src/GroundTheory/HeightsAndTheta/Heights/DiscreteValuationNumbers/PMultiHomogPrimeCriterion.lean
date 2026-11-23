module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import Mathlib.Tactic.Continuity
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
public import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace MultiHomogPrimeCriterion

variable {K : Type} [Fintype K] [DecidableEq K]

def lexDeg : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun b := toLex fun j => b ((Fintype.equivFin K).symm j)
  map_zero' := rfl
  map_add' _ _ := rfl

omit [DecidableEq K] in
lemma lexDeg_injective : Function.Injective (lexDeg (K := K)) := by
  intro a b h
  funext k
  have := congrFun (congrArg ofLex h) (Fintype.equivFin K k)
  change a ((Fintype.equivFin K).symm (Fintype.equivFin K k)) =
    b ((Fintype.equivFin K).symm (Fintype.equivFin K k)) at this
  simpa using this

omit [DecidableEq K] in
lemma lexDeg_surjective : Function.Surjective (lexDeg (K := K)) := by
  intro i
  refine ⟨fun k => ofLex i (Fintype.equivFin K k), ?_⟩
  show toLex _ = i
  rw [← toLex_ofLex i]
  congr 1
  funext j
  simp

variable {ι : K → Type} {R : Type u} [CommRing R]

lemma weight_lexDeg (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexDeg ∘ blockWeight ι) d = lexDeg (Finsupp.weight (blockWeight ι) d) := by
  simp only [Finsupp.weight_apply, map_finsuppSum, map_nsmul, Function.comp_apply]

lemma component_lexDeg (b : K → ℕ) (f : MRing ι R) :
    weightedHomogeneousComponent (lexDeg ∘ blockWeight ι) (lexDeg b) f =
      weightedHomogeneousComponent (blockWeight ι) b f := by
  ext d
  simp only [coeff_weightedHomogeneousComponent, weight_lexDeg, lexDeg_injective.eq_iff]

lemma isMultiHomog_of_lex {x : MRing ι R} {i : Lex (Fin (Fintype.card K) → ℕ)}
    (hx : IsWeightedHomogeneous (lexDeg ∘ blockWeight ι) x i) : ∃ s, IsMultiHomog x s := by
  obtain ⟨b, rfl⟩ := lexDeg_surjective i
  refine ⟨b, fun d hd => ?_⟩
  have h := hx hd
  rw [weight_lexDeg] at h
  exact lexDeg_injective h


omit [Fintype K] [DecidableEq K] in
lemma coe_decompose {σ M : Type*} [AddCommMonoid M] {_ : DecidableEq M} (w : σ → M)
    [GradedRing (weightedHomogeneousSubmodule R w)] (r : MvPolynomial σ R) (i : M) :
    (DirectSum.decompose (weightedHomogeneousSubmodule R w) r i : MvPolynomial σ R) =
      weightedHomogeneousComponent w i r := by
  classical
  have hfin := weightedHomogeneousComponent_finsupp (w := w) r
  conv_lhs => rw [← sum_weightedHomogeneousComponent w r, finsum_eq_sum _ hfin]
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_eq_single i]
  · exact DirectSum.decompose_of_mem_same _ (weightedHomogeneousComponent_mem w r i)
  · intro m _ hm
    exact DirectSum.decompose_of_mem_ne _ (weightedHomogeneousComponent_mem w r m) hm
  · intro hi
    have h0 : weightedHomogeneousComponent w i r = 0 := by
      by_contra h
      exact hi ((Set.Finite.mem_toFinset hfin).2 h)
    rw [h0, DirectSum.decompose_zero]
    rfl

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem proof : MultiHomogPrimeCriterion.Statement := by
  intro R _ K _ _ ι Q hQ hne hform
  refine Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
    (𝒜 := weightedHomogeneousSubmodule R (lexDeg ∘ blockWeight ι)) ?_ hne ?_
  · intro i r hr
    obtain ⟨b, rfl⟩ := lexDeg_surjective i
    rw [coe_decompose, component_lexDeg]
    exact hQ r hr b
  · rintro x y ⟨i, hx⟩ ⟨j, hy⟩ hxy
    obtain ⟨sa, ha⟩ := isMultiHomog_of_lex hx
    obtain ⟨sb, hb⟩ := isMultiHomog_of_lex hy
    exact hform x y sa sb ha hb hxy

end MultiHomogPrimeCriterion

end

end GroundTheory.Heights₂.Heights.NumbersDVR
