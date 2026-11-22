module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjAction
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmDatumFormSqrtNegDPurePeriod
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsTenBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.T2SpacePtsOverOfIsSeparated
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteDimensionalField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CMExistsCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

section Triples

variable {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}

theorem sab_lbIso {f : S' ⟶ S} (m : SABMap t' t f) : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem exists_ptEquiv {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {x' : T ⟶ S'} {x : T ⟶ S} (h : x' ≫ f = x) :
    ∃ p : (Over.mk x' ⟶ t'.G) ≃* (Over.mk x ⟶ t.G), ∀ u, (p u).left = u.left ≫ m.φ :=
  LiePull.exists_pushEquiv m.cart (Over.mk x') x h.symm

theorem pt_ext {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {u v : T ⟶ t'.G.left} (h₁ : u ≫ m.φ = v ≫ m.φ)
    (h₂ : u ≫ t'.G.hom = v ≫ t'.G.hom) : u = v :=
  m.cart.1.hom_ext h₁ h₂

end Triples

section Extend

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

theorem spMap_int (j : K →+* K') {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : σ'.comp j = σ) :
    spMap (σ'.comp (algebraMap (𝓞 K') K')) ≫ spMap (RingOfIntegers.mapRingHom j) =
      spMap (σ.comp (algebraMap (𝓞 K) K)) := by
  rw [spMap_comp', ← h]
  rfl

end Extend

section Conclusions

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Pe : D'.La →+ (Fin g → ℂ)} {hP : IsPeriod D' ty Pe}

variable {Xo} {Z : CMLat hP D.p D.q} {x : Sp ℂ ⟶ Xo.X} {e : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)}
  {K' : Type} [Field K'] [NumberField K'] {κ : KA l →+* K'} {σ' : K' →+* ℂ} {k : IntermediateField ℚ ℂ}

end Conclusions

section ChangeOfExp

variable {D₁ D₂ : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)}

end ChangeOfExp

section Point

end Point

section Tensor

end Tensor

end GlobalTheory.CMExistsCompare
end
