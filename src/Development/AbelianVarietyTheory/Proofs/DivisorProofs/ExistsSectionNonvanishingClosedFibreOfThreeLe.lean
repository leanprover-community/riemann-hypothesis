module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExpansionWeightZeroCoefficientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNotVanishingClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOfExpansionModMaximalIdealStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.ClosedFibreBpf

theorem thick_zero_apply (R : Type) [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) :
    thick R (maximalIdeal R) 0 z = closedPoint R := by
  show (Spec.map _).base z = _
  rw [Spec.map_base]
  apply PrimeSpectrum.ext
  show Ideal.comap _ z.asIdeal = maximalIdeal R
  symm
  apply (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (by
    haveI := z.isPrime
    exact Ideal.IsPrime.ne_top inferInstance)
  intro a ha
  show _ ∈ z.asIdeal
  have : (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) a = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]; simpa using ha
  rw [show (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))).hom a = 0 from this]
  exact z.asIdeal.zero_mem

theorem exists_sec_ne_zero_at : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 3 ≤ k → ∀ y : (thickObj R (maximalIdeal R) 0 G).left, ∃ (s : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  intro R _ _ _ hB D A G _ _ hG U k hk y
  obtain ⟨σ, j, hx⟩ := GlobalTheory.T.exists_weightZero_section_not_vanishing_closedFibre R hB D k (by omega) ((U.gt 0).pG.left y) (by
    have h := congrArg (fun f => f.base y) (Over.w (U.gt 0).pG)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    exact h.trans (thick_zero_apply R _))
  obtain ⟨s, f, hf0, hfα, hexp⟩ := GlobalTheory.T.exists_section_expansion_weightZero_coefficient R hB D A G hG U k (by omega) σ
  obtain ⟨i, hi⟩ := GlobalTheory.T.section_nonzero_of_expansion_mod_maximalIdeal R D A G U.toUnifPre k s f hexp hfα y ⟨j, by
    subst hf0
    rw [← Scheme.preimage_basicOpen]
    exact hx⟩
  exact ⟨s, i, hi⟩

end GlobalTheory.Mum.ClosedFibreBpf
