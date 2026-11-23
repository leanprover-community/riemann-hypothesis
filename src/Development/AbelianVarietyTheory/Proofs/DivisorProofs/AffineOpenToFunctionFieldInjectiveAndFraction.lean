module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.GenFrac

theorem injective_and_frac : ∀ (X : Scheme.{0}) (V : X.Opens) [IsIntegral V.toScheme] (W : X.affineOpens), W.1 ≤ V → ∀ (ρW : Γ(X, W.1) →+* V.toScheme.functionField), spMap ρW ≫ GlobalTheory.LogKS.chart W = V.toScheme.fromSpecStalk (genericPoint V.toScheme) ≫ V.ι → Function.Injective ρW ∧ ∀ x : V.toScheme.functionField, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a := by
  intro X V _ W hWV ρW h
  set η := genericPoint V.toScheme with hη
  have hx : V.ι η ∈ W.1 := by
    have h1 := congrArg (fun f : Spec (V.toScheme.presheaf.stalk η) ⟶ X =>
      f (IsLocalRing.closedPoint (V.toScheme.presheaf.stalk η))) h
    have h3 : (V.toScheme.fromSpecStalk η ≫ V.ι)
        (IsLocalRing.closedPoint (V.toScheme.presheaf.stalk η)) = V.ι η :=
      congrArg V.ι (Scheme.fromSpecStalk_closedPoint (x := η))
    rw [← h1.trans h3]
    have h2 : Set.range (W.2.fromSpec) = (W.1 : Set X) := W.2.range_fromSpec
    rw [← SetLike.mem_coe, ← h2]
    exact ⟨_, rfl⟩
  have he : CommRingCat.ofHom ρW = X.presheaf.germ W.1 (V.ι η) hx ≫ V.ι.stalkMap η := by
    apply Spec.map_injective
    have hW : IsAffineOpen W.1 := W.2
    haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
    rw [← cancel_mono hW.fromSpec, Spec.map_comp, Category.assoc]
    refine Eq.trans h ?_
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← W.2.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  have he' : ∀ a, ρW a = V.ι.stalkMap η (X.presheaf.germ W.1 (V.ι η) hx a) := fun a =>
    congrArg (fun f : Γ(X, W.1) ⟶ V.toScheme.presheaf.stalk η => f a) he
  have hbij : Function.Bijective (V.ι.stalkMap η) := ConcreteCategory.bijective_of_isIso _
  refine ⟨?_, fun x => ?_⟩
  · have hiso : IsIso (V.ι.app W.1) := V.ι.isIso_app W.1 (by simpa using hWV)
    have hinj1 : Function.Injective (V.ι.app W.1) := (ConcreteCategory.bijective_of_isIso _).1
    have hinj2 := germ_injective_of_isIntegral V.toScheme (U := V.ι ⁻¹ᵁ W.1) η hx
    intro a b hab
    rw [he', he', Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply] at hab
    exact hinj1 (hinj2 hab)
  · obtain ⟨y, rfl⟩ := hbij.2 x
    letI : Algebra Γ(X, W.1) (X.presheaf.stalk (V.ι η)) :=
      (X.presheaf.germ W.1 (V.ι η) hx).hom.toAlgebra
    haveI : IsLocalization.AtPrime (X.presheaf.stalk (V.ι η))
        (W.2.primeIdealOf ⟨V.ι η, hx⟩).asIdeal := W.2.isLocalization_stalk ⟨V.ι η, hx⟩
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj
      (W.2.primeIdealOf ⟨V.ι η, hx⟩).asIdeal.primeCompl y
    have hu := IsLocalization.map_units (X.presheaf.stalk (V.ι η)) b
    refine ⟨a, b, ?_, ?_⟩
    · rw [he']
      exact (hu.map (V.ι.stalkMap η).hom).ne_zero
    · rw [he', he']
      exact (map_mul (V.ι.stalkMap η).hom _ _).symm.trans (congrArg (V.ι.stalkMap η) hab)

end GlobalTheory.GenFrac
