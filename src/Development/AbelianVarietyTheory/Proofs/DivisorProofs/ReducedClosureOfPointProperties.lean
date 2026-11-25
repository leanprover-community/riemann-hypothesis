module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.ClosFacts

theorem range_closι {X : Scheme.{0}} (z : X) : range (closι z) = closure {z} :=
  range_redι (Closeds.closure {z})

theorem isIntegral_clos {X : Scheme.{0}} (z : X) : IsIntegral (clos z) :=
  isIntegral_red (Z := Closeds.closure {z}) isIrreducible_singleton.closure

theorem clos_facts : ∀ (X : Scheme.{0}) (z : X), ∃ _ : IsIntegral (clos z), closι z (genericPoint (clos z)) = z ∧ topologicalKrullDim (clos z) = topologicalKrullDim (closure ({z} : Set X)) ∧ ∀ (Y : Scheme.{0}) [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = z → ∃ g : Y ⟶ clos z, g ≫ closι z = π ∧ g (genericPoint Y) = genericPoint (clos z) ∧ g.residueDegree (genericPoint Y) = π.residueDegree (genericPoint Y) ∧ (IsClosedImmersion π → IsIso g) := by
  intro X z
  have hI := isIntegral_clos z
  have hr := range_closι z
  have hi : closι z (genericPoint (clos z)) = z := by
    have h₁ := (genericPoint_spec (clos z)).image (closι z).continuous
    rw [image_univ, hr, closure_closure] at h₁
    exact h₁.eq isGenericPoint_closure
  refine ⟨hI, hi, (topologicalKrullDim_eq_of_isEmbedding (closι z).isClosedEmbedding.isEmbedding hr), ?_⟩
  intro Y _ π hπ
  have : Surjective (Limits.pullback.snd (closι z) π) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr, ← hπ]
    exact eq_univ_of_forall fun y => ((genericPoint_specializes y).map π.continuous).mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd (closι z) π)
  obtain ⟨g, rfl⟩ : ∃ g : Y ⟶ clos z, g ≫ closι z = π :=
    ⟨inv (Limits.pullback.snd (closι z) π) ≫ Limits.pullback.fst (closι z) π, by
      rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]⟩
  have hg : g (genericPoint Y) = genericPoint (clos z) :=
    (closι z).isClosedEmbedding.injective (hπ.trans hi.symm)
  refine ⟨g, rfl, hg, ?_, fun hc => ?_⟩
  · rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion (closι z), one_mul]
  · have : IsClosedImmersion g := IsClosedImmersion.of_comp_isClosedImmersion g (closι z)
    have : Surjective g := ⟨by
      rw [← Set.range_eq_univ]
      have h₁ := (genericPoint_spec Y).image g.continuous
      rw [image_univ, g.isClosedEmbedding.isClosed_range.closure_eq, hg] at h₁
      exact h₁.def.symm.trans (genericPoint_spec (clos z)).def⟩
    exact isIso_of_isClosedImmersion_of_surjective g

end GlobalTheory.ClosFacts
