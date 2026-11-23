module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSquareEquivFibreSquareSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitBasicOpenOfCoboundaryIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFaithfullyFlatAlgebraOverAffineOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90LocalOfCocycleTensorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleDescendsOnTripleOverlapsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LBDescent

theorem coboundary_locally_of_cocycle : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
    (V : Y.Opens) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
    (∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c) →
    ∀ y ∈ V, ∃ V' : Y.Opens, V' ≤ V ∧ y ∈ V' ∧ ∃ u : Γ(X, f ⁻¹ᵁ V')ˣ,
      ∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u := by
  intro X Y f _ _ _ _ V c hc y hy
  obtain ⟨V₀, hV₀, hyV₀, hV₀V⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hy
  have h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀ := fun z hz => by
    show f (pullback.snd f f z) ∈ V₀
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hz
  have hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V := fun z hz => hV₀V hz
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  obtain ⟨hN, hF, hFF⟩ := GlobalTheory.T.finite_faithfullyFlat_algebra_over_affine_open f V₀ hV₀
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_tensorSquare_equiv_fibreSquare_sections f V₀ hV₀ h
  have hcoc := GlobalTheory.T.unit_cocycle_descends_on_triple_overlaps f V V₀ hV₀ h hle c hc e he
  let c₀ : (Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀))ˣ := Units.map e.symm.toMonoidHom (res hle c)
  obtain ⟨r, hr, m, s, n, hm, hs⟩ := GlobalTheory.T.hilbert90_of_cocycle_faithfullyFlat_tensor _ _ c₀ hcoc
    (Ideal.comap (Y.presheaf.germ V₀ y hyV₀).hom (IsLocalRing.maximalIdeal _)) inferInstance
  have hm' : ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom m * (res hle c).val =
      ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom m := by
    have := congrArg e hm
    rw [map_mul, he, he] at this
    simpa [c₀] using this
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_basicOpen_of_coboundary_identity f V V₀ h hle c r m s n hm' hs
  refine ⟨Y.basicOpen r, (Y.basicOpen_le r).trans hV₀V, ?_, u, hu⟩
  rw [Scheme.mem_basicOpen _ _ _ hyV₀]
  by_contra hh
  exact hr (by simpa [IsLocalRing.mem_maximalIdeal] using hh)

end GlobalTheory.LBDescent
