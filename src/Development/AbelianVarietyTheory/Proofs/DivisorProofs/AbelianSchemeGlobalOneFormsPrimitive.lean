module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsProjectiveRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfSplitInjectiveFgProjectiveConstantRanStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgProjectiveConstantRankExtensionAndProdStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjectionsStatement
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.AbCoh

theorem primF_of_abelian (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) : PrimF A := by
  obtain ⟨-, -, hAA, hsAA⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  have hax := (GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A).2.1
  have hM : FP R (GlobForm A.hom × GlobForm A.hom) (g + g) :=
    (GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod).2 R _ _ g g (GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hs) (GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hs)
  have hN : FP R (GlobForm (A ⊗ A).hom) (g + g) := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R (A ⊗ A) (g + g) hAA hsAA
  let i₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  let i₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  let f : (GlobForm A.hom × GlobForm A.hom) →ₗ[R] GlobForm (A ⊗ A).hom :=
    (pF (fst A A)).coprod (pF (snd A A))
  let r : GlobForm (A ⊗ A).hom →ₗ[R] (GlobForm A.hom × GlobForm A.hom) :=
    (pF i₁).prod (pF i₂)
  have hr : ∀ y, r y = (pF i₁ y, pF i₂ y) := fun y ↦ by simp [r, LinearMap.prod_apply, Function.prod]
  have hrf : ∀ x, r (f x) = x := by
    rintro ⟨a, b⟩
    obtain ⟨h1, h2, -, h4, h5, -⟩ := hax a
    obtain ⟨k1, k2, -, k4, k5, -⟩ := hax b
    have hf : f (a, b) = pF (fst A A) a + pF (snd A A) b := by simp [f]
    rw [hr, hf, map_add (f := _), map_add (f := _), h1, k2, h4, k5, add_zero, zero_add]
  have hbij := GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank R _ _ (g + g) hM hN f r hrf
  have hrinj : Function.Injective r := by
    intro y y' h
    obtain ⟨x, rfl⟩ := hbij.2 y
    obtain ⟨x', rfl⟩ := hbij.2 y'
    rw [hrf, hrf] at h; rw [h]
  intro x
  obtain ⟨-, -, h3, -, -, h6⟩ := hax x
  have e1 : r (pF μ[A] x) = (x, x) := (hr _).trans (Prod.ext h3 h6)
  exact (hrinj (e1.trans (hrf (x, x)).symm)).trans (LinearMap.coprod_apply _ _ _)

end GlobalTheory.AbCoh
