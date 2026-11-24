module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem clo_restrict_dominant : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) (y : Y), ∃ g : clo y ⟶ clo (π y), g ≫ cloι (π y) = cloι y ≫ π ∧ g (genericPoint _) = genericPoint _ ∧ ∀ w : clo y, g.residueDegree w = π.residueDegree (cloι y w) := by
  intro X Y π y
  set i := cloι (π y)
  set j := cloι y
  have hi : i (genericPoint (clo (π y))) = π y := cloι_genericPoint _
  have hj : j (genericPoint (clo y)) = y := cloι_genericPoint _
  have hr : Set.range i = closure {π y} := by
    have h₁ := (genericPoint_spec (clo (π y))).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  have : Surjective (Limits.pullback.snd i (j ≫ π)) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]
    refine Set.eq_univ_of_forall fun w => ?_
    have := ((genericPoint_specializes w).map (j ≫ π).continuous)
    rw [Set.mem_preimage]
    have e : (j ≫ π) (genericPoint (clo y)) = π y := by
      rw [Scheme.Hom.comp_apply, hj]
    rw [e] at this
    exact this.mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i (j ≫ π))
  refine ⟨inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π), ?_, ?_, ?_⟩
  · rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]
  · apply i.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      Scheme.Hom.comp_apply, hj, hi]
  · intro w
    have e₁ := GlobalTheory.CurveDegreesCompare.residueDegree_comp (inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π)) i w
    have e₂ := GlobalTheory.CurveDegreesCompare.residueDegree_comp j π w
    rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      GlobalTheory.Published.residueDegree_of_isClosedImmersion i, one_mul] at e₁
    rw [GlobalTheory.Published.residueDegree_of_isClosedImmersion j, mul_one] at e₂
    rw [← e₁, e₂]

end GlobalTheory.MixHt
