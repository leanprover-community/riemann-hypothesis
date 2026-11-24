module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelActionTripleOverlapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelActionIsPullbackProdMapTorsorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyTrivialUnitCocycleSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

theorem exists_nhds_charUnit : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → ∀ y : (A' ⊗ T).left, ∃ V : (A' ⊗ T).left.Opens, y ∈ V ∧ ∃ e : Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ V)ˣ, ∀ (W : (A ⊗ (N ⊗ T)).left.Opens) (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)) (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)), res h₁ (pullU (actMap i T).left _ e) = res le_top (pullTop (snd A (N ⊗ T)).left χ) * res h₂ (pullU (prMap A N T).left _ e) := by
  intro S A A' N T _ _ _ i q χ hi hq hfin hflat hsurj hk hχ y
  have hpb := GlobalTheory.T.kernelAction_isPullback_prodMap_torsor S A A' N T i q hi hq hk
  have hpb' : IsPullback (prMap A N T).left (actMap i T).left (pmap q T).left (pmap q T).left :=
    hpb.map (Over.forget S)
  obtain ⟨W, m₁₂, m₂₃, m₁₃, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_kernelAction_triple_overlap S A N T i χ hi hχ
  have hpq : pmap q T = q ▷ T := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [pmap]
  have hsq := GlobalTheory.SemiRigid.isPullback_whiskerRight q T
  have hA : IsAffineHom (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  have hF : Flat (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  have hS : Surjective (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  exact GlobalTheory.T.locally_trivial_unit_cocycle_scheme _ _ _ _ (pmap q T).left (actMap i T).left (prMap A N T).left m₁₂ m₂₃ m₁₃ _
    hA hF hS hpb' h1 h2 h3 h4 y

end GlobalTheory.CharKer
