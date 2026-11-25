module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGeneric
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem eq_of_isIso_restrict {W X' : Scheme.{0}} (f : X' ⟶ W) (U : W.Opens) (hU : IsIso (f ∣_ U)) {y y' : X'}
    (hy : f y ∈ U) (hy' : f y' ∈ U) (e : f y = f y') : y = y' := by
  haveI := IsOpenImmersion.of_isIso (f ∣_ U)
  let a : (f ⁻¹ᵁ U : Scheme) := ⟨y, hy⟩
  let a' : (f ⁻¹ᵁ U : Scheme) := ⟨y', hy'⟩
  have h : (f ∣_ U) a = (f ∣_ U) a' :=
    Subtype.ext (by rw [morphismRestrict_base_coe, morphismRestrict_base_coe]; exact e)
  exact congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective h)

theorem exists_lift_isCptGen : ∀ (W X' : Scheme.{0}) (f : X' ⟶ W) (U : W.Opens) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W),
    IsIso (f ∣_ U) → genPt ξ ∈ U → IsCptGen ξ → (∀ x : X', IsDomain (X'.presheaf.stalk x)) →
    ∃ ξ' : Sp Ω ⟶ X', ξ' ≫ f = ξ ∧ IsCptGen ξ' := by
  intro W X' f U Ω _ ξ hiso hU hξ hdom
  obtain ⟨hb, -⟩ := hξ
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint Ω)]
    exact hU
  let ξ' : Sp Ω ⟶ X' := IsOpenImmersion.lift U.ι ξ hr ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hfac : ξ' ≫ f = ξ := by
    simp only [ξ', Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]
  have hfg : f (genPt ξ') = genPt ξ := by
    have h3 := Scheme.Hom.comp_apply ξ' f (IsLocalRing.closedPoint Ω)
    rw [hfac] at h3
    exact h3.symm
  have hmem : genPt ξ' ∈ f ⁻¹ᵁ U := by
    show f (genPt ξ') ∈ U
    rw [hfg]; exact hU
  refine ⟨ξ', hfac, ?_⟩
  refine isCptGen_of_maximal_of_surjective hdom ξ' ?_ ?_
  · intro y hy
    have hyU : y ∈ f ⁻¹ᵁ U := hy.mem_open (f ⁻¹ᵁ U).isOpen hmem
    have h1 : f y ⤳ genPt ξ := hfg ▸ hy.map f.continuous
    obtain ⟨q, hq⟩ : f y ∈ Set.range (W.fromSpecStalk (genPt ξ)) := by
      rw [Scheme.range_fromSpecStalk]; exact h1
    have hq' : q = IsLocalRing.closedPoint _ :=
      (PrimeSpectrum.comapEquiv (RingEquiv.ofBijective _ hb)).injective (Subsingleton.elim _ _)
    rw [hq', Scheme.fromSpecStalk_closedPoint] at hq
    exact eq_of_isIso_restrict f U hiso hyU hmem (hq.symm.trans hfg.symm)
  · have hcomp := hb.2
    rw [← hfac, Scheme.stalkClosedPointTo_comp] at hcomp
    exact Function.Surjective.of_comp (g := (Scheme.Hom.stalkMap f _).hom) hcomp

end GlobalTheory.CompanionTheory.Ar.SncBase
