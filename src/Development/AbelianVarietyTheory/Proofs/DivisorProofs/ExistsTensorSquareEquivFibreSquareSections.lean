module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBDescent

theorem exists_tensorSquare_equiv_sections {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (V₀ : Y.Opens)
    (hV₀ : IsAffineOpen V₀)
    (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀) :
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    ∃ e : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀) ≃+* Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
      ∀ a b : Γ(X, f ⁻¹ᵁ V₀), e (a ⊗ₜ b) =
        ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a * ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b := by
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  have hV' : IsAffineOpen (f ⁻¹ᵁ V₀) := hV₀.preimage f
  have P := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE (IsPullback.of_hasPullback f f).flip
    inferInstance hV₀ hV' le_rfl h
  rw [Scheme.Hom.appLE_eq_app] at P
  have T := CommRingCat.isPushout_tensorProduct Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) Γ(X, f ⁻¹ᵁ V₀)
  let I := IsPushout.isoIsPushout _ _ T P.flip
  refine ⟨I.commRingCatIsoToRingEquiv, fun a b => ?_⟩
  have h1 : I.hom.hom (a ⊗ₜ 1) = ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a :=
    congrArg (fun t => t.hom a) (IsPushout.inl_isoIsPushout_hom _ _ T P.flip)
  have h2 : I.hom.hom (1 ⊗ₜ b) = ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b :=
    congrArg (fun t => t.hom b) (IsPushout.inr_isoIsPushout_hom _ _ T P.flip)
  have hab : (a ⊗ₜ[Γ(Y, V₀)] b : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) = (a ⊗ₜ 1) * (1 ⊗ₜ b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
  change I.hom.hom (a ⊗ₜ b) = _
  rw [hab, map_mul, h1, h2]

end GlobalTheory.LBDescent
