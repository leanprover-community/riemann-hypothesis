module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Limits (pullback)
open GlobalTheory.VB Formalism.BasicNotions
open GlobalTheory.LieVB (omega omegaBase)
open GlobalTheory.Vert (SmallPic smallPicEquiv)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol IsProjSurface degCh2)
open scoped CategoryTheory.Obj

namespace GlobalTheory.ShFam.Pad

namespace ProjCode

variable {R : Type} [CommRing R] (C : ProjCode R)

instance algebra : Algebra R Γ(C.X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ C.str.appTop).hom.toAlgebra

end ProjCode

abbrev toSpZ (Y : Scheme.{0}) : Y ⟶ Sp ℤ := specZIsTerminal.from Y

theorem isProjOver_toSpZ {R : Type} [CommRing R] [Module.Finite ℤ R] {Y : Scheme.{0}}
    {f : Y ⟶ Sp R} (h : IsProjOver f) : IsProjOver (toSpZ Y) := by
  obtain ⟨N, i, hi, -⟩ := h
  have hb : IsFinite (spMap (Int.castRingHom R)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := R)).2 inferInstance
  have P := GlobalTheory.ProjSpace.isPullback_baseChange N (Int.castRingHom R)
  have hf : IsFinite (GlobalTheory.ProjSpace.baseChange N (Int.castRingHom R)) :=
    MorphismProperty.of_isPullback P.flip hb
  have := isProjOver_comp_of_finite ℤ (PSpace ℤ N) Y
    (i ≫ GlobalTheory.ProjSpace.baseChange N (Int.castRingHom R)) (PSpace.str ℤ N) inferInstance
    ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  exact specZIsTerminal.hom_ext _ (toSpZ Y) ▸ this

theorem isArithVar_toSpZ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : IsArithVar (toSpZ Y) D :=
  have := h.finite
  ⟨inferInstance, inferInstance, h.isIntegral, isProjOver_toSpZ h.isProjOver,
    specZIsTerminal.hom_ext (p ≫ spMap (Int.castRingHom k))
      (toSpZ Y ≫ spMap (Int.castRingHom ℤ)) ▸ h.flat, h.dim_eq⟩

namespace PPCode

variable {S S' : Scheme.{0}}

end PPCode

namespace Surf

variable (s : Surf)

end Surf

namespace SurfFp

attribute [instance] prime

variable (s : SurfFp)

end SurfFp

namespace SurfSt

variable {D : D7}

end SurfSt

variable {D : D7} {X : DivX D}

end GlobalTheory.ShFam.Pad
