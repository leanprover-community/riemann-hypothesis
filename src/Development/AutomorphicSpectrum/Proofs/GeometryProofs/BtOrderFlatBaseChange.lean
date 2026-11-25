module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExtensionOrderEqSpan
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSet
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSection
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFlat

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.FlatBC

section Alg

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']

def kapL (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    FractionRing R →ₗ[R] FractionRing R' where
  toFun := κ
  map_add' := map_add κ
  map_smul' r x := by
    have := congr($hκ r)
    simp only [RingHom.comp_apply] at this
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply, this,
      IsScalarTower.algebraMap_apply R R' (FractionRing R')]

end Alg

section Sch

lemma top_le_pre {X Y : Scheme.{0}} (x : X ⟶ Y) : (⊤ : X.Opens) ≤ x ⁻¹ᵁ ⊤ := by simp

lemma valAt_map {A B : Type} [CommRing A] [CommRing B] (κ : A →+* B) {X : Scheme.{0}}
    (y : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ y) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ y) U h' s = κ (valAt y U h s) := by
  rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_comp _ y U ⊤ h (top_le_pre _), PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_spec]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

lemma valAt_const (Γ : QFGroup R T) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤) (h' : ⊤ ≤ Γ.G.hom ⁻¹ᵁ ⊤)
    (c : Γ(Spec (CommRingCat.of R), ⊤)) :
    valAt (Γ.pt t).left ⊤ h ((Γ.G.hom.appLE ⊤ ⊤ h').hom c) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) := by
  have e : (Γ.pt t).left ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    Over.w (Γ.pt t)
  rw [← PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_comp (Γ.pt t).left Γ.G.hom ⊤ ⊤ h' h (top_le_pre _), PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_congr e _ _ (top_le_pre _), PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_spec]

def secFn (Γ : QFGroup R T) : Submodule R (T → FractionRing R) where
  carrier := {f | ∃ s : Γ(Γ.G.left, ⊤), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤),
    valAt (Γ.pt t).left ⊤ h s = f t}
  add_mem' := by
    rintro f f' ⟨s, hs⟩ ⟨s', hs'⟩
    exact ⟨s + s', fun t h => by rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_add, hs, hs']; rfl⟩
  zero_mem' := ⟨0, fun t h => by rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_zero]; rfl⟩
  smul_mem' := by
    rintro r f ⟨s, hs⟩
    refine ⟨(Γ.G.hom.appLE ⊤ ⊤ (top_le_pre _)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * s,
      fun t h => ?_⟩
    rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.valAt_mul, valAt_const, hs]
    simp [Algebra.smul_def]

variable {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R']

lemma btOrder_le_ext [Finite T] [Module.Flat R R'] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    Γ'.btOrder ⊤ ≤ extOrder (algebraMap R R') (Γ.btOrder ⊤) := by
  intro g hg
  rw [_root_.GlobalTheory.CompanionTheory.Ar.BT.ExtSpan.extOrder_eq_span]
  refine PositivityTheory.HtPt.Htat.ValuationInjectivePi.alg_core κ hκ (secFn Γ) (Subalgebra.toSubmodule (Γ.btOrder ⊤)) (fun f => mem_btOrder_iff Γ f) g ?_
  intro t
  obtain ⟨x, hx⟩ := (mem_btOrder_iff Γ' g).1 hg t
  have e : (fun h => algebraMap R' (FractionRing R') (g (t * h))) =
      fun h => valAt (Γ'.pt h).left ⊤ (top_le_pre _) x := by
    funext h
    exact (hx h _).symm
  rw [e]
  exact val_mem_span Γ Γ' F hbc κ hκ x

lemma ext_le_btOrder [Finite T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    extOrder (algebraMap R R') (Γ.btOrder ⊤) ≤ Γ'.btOrder ⊤ :=
  by apply _root_.PositivityTheory.HtPt.Htat.ValuationInjectivePi.ext_le_btOrder <;> assumption

end Sch

theorem btOrder_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → Γ'.btOrder ⊤ = extOrder (algebraMap R R') (Γ.btOrder ⊤) :=
  PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange

end GlobalTheory.CompanionTheory.Ar.BT.FlatBC
