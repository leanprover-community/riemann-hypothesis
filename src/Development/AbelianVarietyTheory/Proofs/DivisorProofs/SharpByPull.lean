import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEighthPowerGroupPullback

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementaryMatrixEndomorphism_groupPullback_transport : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (a b : Fin 8) (f₁ : B ⟶ B) (f₁' : B' ⟶ B'), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ w, (pr' w).left ≫ χ = φB ≫ (pr w).left) → f₁'.left ≫ φB = φB ≫ f₁.left → MatEnd pr a b f₁ → MatEnd pr' a b f₁' := by
  first | exact @GlobalTheory.MatEndPull.matEnd_pull | exact GlobalTheory.MatEndPull.matEnd_pull | (intros; apply GlobalTheory.MatEndPull.matEnd_pull <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPowerProjections_groupPullback : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ C)), ∃! x : T₁ ⟶ B, ∀ a, x ≫ pr a = y a) → ∃ pr' : Fin 8 → (B' ⟶ C'), (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) ∧ (∀ a, IsMonHom (pr' a)) ∧ ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ C')), ∃! x : T₁ ⟶ B', ∀ a, x ≫ pr' a = y a := by
  first | exact @GlobalTheory.GrpPullPow.pr_pull | exact GlobalTheory.GrpPullPow.pr_pull | (intros; apply GlobalTheory.GrpPullPow.pr_pull <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_eighthPower_groupPullback : ∀ {T T' : Scheme.{0}} {B C : Over T} {B' C' : Over T'} {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} {χ₂ : (C' ⊗ C').left ⟶ (C ⊗ C).left} (Q : LB (C ⊗ C).left) (Q' : LB (C' ⊗ C').left) (L : LB B.left) (L' : LB B'.left) (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (W : Matrix (Fin 8) (Fin 8) ℤ), Q.IsLB → Q'.IsLB → L.IsLB → L'.IsLB → IsSquare χ χ₂ → LBIso Q' (Q.pull χ₂) → (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) → LBIso L' (L.pull φB) → LBIso L (LB.LinComb Q (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → LBIso L' (LB.LinComb Q' (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) := by
  first | exact @GlobalTheory.Poinc.Eq8.lbIso_eighth_pull | exact GlobalTheory.Poinc.Eq8.lbIso_eighth_pull | (intros; apply GlobalTheory.Poinc.Eq8.lbIso_eighth_pull <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section
namespace GlobalTheory.GenPb

theorem genfib_grpPullback : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm ∧ ψ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ ξ₀ ∧ IsGrpPullback A'.A ρ.P.A (ξ₀ ≫ FinalForm.u₀) (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G' _ _ D' A' U' ξ gm hgm ξ₀ hξ
  have := U'.gen_hom
  have : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
  have gpA : IsGrpPullback A'.A G' (jK R) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) :=
    ((isGrpPullback_of_iso U'.gen.symm).comp (isGrpPullback_pullback G' (jK R))).congr
      (Category.id_comp _) rfl
  have h2 : IsGrpPullback A'.A FinalForm.G (ξ₀ ≫ U₀.ι) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ gm) :=
    (gpA.comp hgm).congr hξ.symm rfl
  have hw : (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) ≫ FinalForm.G.hom = (A'.A.hom ≫ ξ₀) ≫ U₀.ι := by
    have := h2.1.w
    simpa [Category.assoc] using this
  refine ⟨FinalForm.cart.1.lift (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) (A'.A.hom ≫ ξ₀) hw,
    FinalForm.cart.1.lift_fst _ _ _, FinalForm.cart.1.lift_snd _ _ _, ?_⟩
  have h3 : IsGrpPullback A'.A ((Over.pullback FinalForm.u₀).obj ρ.P.A) ξ₀
      (FinalForm.cart.1.lift (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) (A'.A.hom ≫ ξ₀) hw) :=
    IsGrpPullback.cancel FinalForm.cart (h2.congr rfl (by rw [FinalForm.cart.1.lift_fst, Category.assoc]))
      (FinalForm.cart.1.lift_snd _ _ _)
  exact h3.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)

end GlobalTheory.GenPb
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_uniformisedModelPoint_groupPullback : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm ∧ ψ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ ξ₀ ∧ IsGrpPullback A'.A ρ.P.A (ξ₀ ≫ FinalForm.u₀) (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := by
  atlas_forward_decl GlobalTheory.GenPb.genfib_grpPullback
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section

namespace GlobalTheory.Poinc.GenPull

theorem lbIso_gen_pull : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀), ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → LBIso A'.L (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G' _ _ D' A' U' gm ψ hψ H
  have e0 : LBIso A'.L (A'.L.pull (𝟙 _)) := GlobalTheory.SiegelPullComp.iso_pull_id A'.isLB
  have hc : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have e1 : LBIso ((A'.L.pull U'.gen.hom.left).pull U'.gen.inv.left) (A'.L.pull (𝟙 _)) := by
    have := GlobalTheory.SiegelPullComp.iso_pull_pull A'.isLB U'.gen.hom.left U'.gen.inv.left
    rwa [hc] at this
  have e2 := GlobalTheory.SiegelPullComp.iso_pull U'.gen.inv.left U'.ext
  have e3 := GlobalTheory.SiegelPullComp.iso_pull_pull U'.LG.isLB (pullback.fst G'.hom (jK R)) U'.gen.inv.left
  have e4 := GlobalTheory.SiegelPullComp.iso_pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) H
  have e5 := GlobalTheory.SiegelPullComp.iso_pull_pull FinalForm.L.isLB gm (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R))
  have hq : (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ gm = ψ ≫ FinalForm.φ := by
    rw [Category.assoc, hψ]
  rw [hq] at e5
  have e6 := GlobalTheory.SiegelPullComp.iso_pull_pull FinalForm.L.isLB FinalForm.φ ψ
  have e7 := GlobalTheory.SiegelPullComp.iso_pull ψ (⟨FinalForm.w, FinalForm.w_gen⟩ : LBIso _ _)
  have e8 := GlobalTheory.SiegelPullComp.iso_pull_pull ρ.P.isLB (pullback.fst ρ.P.A.hom FinalForm.u₀) ψ
  have hA := A'.isLB
  have hG := U'.LG.isLB
  have hZ := FinalForm.L.isLB
  have hP := ρ.P.isLB
  refine LBIso.trans hA (pull_isLB (pull_isLB hA _) _) (pull_isLB hP _) (LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _) e0 e1.symm) ?_
  refine LBIso.trans (pull_isLB (pull_isLB hA _) _) (pull_isLB (pull_isLB hG _) _) (pull_isLB hP _) e2 ?_
  refine LBIso.trans (pull_isLB (pull_isLB hG _) _) (pull_isLB hG _) (pull_isLB hP _) e3 ?_
  refine LBIso.trans (pull_isLB hG _) (pull_isLB (pull_isLB hZ _) _) (pull_isLB hP _) e4 ?_
  refine LBIso.trans (pull_isLB (pull_isLB hZ _) _) (pull_isLB hZ _) (pull_isLB hP _) e5 ?_
  refine LBIso.trans (pull_isLB hZ _) (pull_isLB (pull_isLB hZ _) _) (pull_isLB hP _) e6.symm ?_
  exact LBIso.trans (pull_isLB (pull_isLB hZ _) _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) e7 e8

end GlobalTheory.Poinc.GenPull
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_polarisation_eq_eighthPower_pullback : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀), ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → LBIso A'.L (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)) := by
  atlas_forward_decl GlobalTheory.Poinc.GenPull.lbIso_gen_pull
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullAlong

theorem sharpBy_pull {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {T T' : Scheme.{0}} (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (t : T' ⟶ T) (v : T' ⟶ F.X) (hv : t ≫ u = v)
    (c : SiegPre g n ζ (u ≫ F.s)) (pr : Fin 8 → (P.A ⟶ c.A)) (φA : P'.A.left ⟶ P.A.left)
    (hS : SharpBy F W P u c pr) (hA : IsGrpPullback P'.A P.A t φA) (hL : LBIso P'.L (P.L.pull φA)) :
    ∃ (c' : SiegPre g n ζ (v ≫ F.s)) (pr' : Fin 8 → (P'.A ⟶ c'.A)) (χ : c'.A.left ⟶ c.A.left),
      SharpBy F W P' v c' pr' ∧ IsGrpPullback c'.A c.A t χ ∧ ∀ a, (pr' a).left ≫ χ = φA ≫ (pr a).left := by
  subst hv
  obtain ⟨hpb, hmon, huniv, hLc⟩ := hS
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n o o ζ ζ (RingHom.id o) T T' (u ≫ F.s)
    ((t ≫ u) ≫ F.s) t rfl (by rw [hid, Category.comp_id, Category.assoc])).1 c
  have hcomp := GlobalTheory.SiegelPullComp.pb_comp hpb hc'
  obtain ⟨χ, χ₂, hχ, hsq, hP, -⟩ := hc'
  obtain ⟨pr', hpr', hmon', huniv'⟩ := GlobalTheory.T.eighthPowerProjections_groupPullback pr hA hχ hmon huniv
  exact ⟨c', pr', χ, ⟨hcomp, hmon', huniv', GlobalTheory.T.lineBundleIso_eighthPower_groupPullback c.P c'.P P.L P'.L pr pr' W c.isLB c'.isLB P.isLB P'.isLB hsq hP hpr' hL hLc⟩,
    hχ, hpr'⟩

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ c' pr', SharpBy F W A' (ξ₀ ≫ FinalForm.u₀ ≫ u) c' pr' ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (f' : G' ⟶ G'), MatOn FinalForm pr a b f → f'.left ≫ gm = gm ≫ f.left → ∃ f₁ : A'.A ⟶ A'.A, MatEnd pr' a b f₁ ∧ (Over.pullback (jK R)).map f' ≫ U'.gen.hom = U'.gen.hom ≫ f₁ := by
  intro g n o _ ζ F W o' Ω _ _ _ S ρ u c pr hS M U₀ EE FinalForm R _ _ _ _ G' _ _ _ D' A' U' ξ gm hgm hLB ξ₀ hξ₀
  obtain ⟨ψ, hψφ, hψs, hψpb⟩ := GlobalTheory.T.genericFibre_uniformisedModelPoint_groupPullback FinalForm U' ξ gm hgm ξ₀ hξ₀
  have hL := GlobalTheory.T.genericFibre_polarisation_eq_eighthPower_pullback FinalForm U' gm ψ hψφ hLB
  obtain ⟨c', pr', χ, hS', hχ, hpr'⟩ := sharpBy_pull F W ρ.P A' u (ξ₀ ≫ FinalForm.u₀) (ξ₀ ≫ FinalForm.u₀ ≫ u)
    (Category.assoc _ _ _) c pr (ψ ≫ pullback.fst _ _) hS hψpb hL
  refine ⟨c', pr', hS', fun a b f f' hf hff' => ?_⟩
  obtain ⟨-, f₁, hf₁, hf₁φ⟩ := hf
  refine ⟨U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom, ?_, by simp⟩
  refine GlobalTheory.T.elementaryMatrixEndomorphism_groupPullback_transport pr pr' a b f₁ _ hψpb hχ hpr' ?_ hf₁
  have hgi : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have hmapf : ((Over.pullback (jK R)).map f').left ≫ pullback.fst G'.hom (jK R) = pullback.fst G'.hom (jK R) ≫ f'.left :=
    pullback.lift_fst _ _ _
  have hmapf₁ : ((Over.pullback FinalForm.u₀).map f₁).left ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = pullback.fst ρ.P.A.hom FinalForm.u₀ ≫ f₁.left :=
    pullback.lift_fst _ _ _
  have key : (U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom).left ≫ ψ = ψ ≫ ((Over.pullback FinalForm.u₀).map f₁).left := by
    apply FinalForm.cart.1.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [hψφ, reassoc_of% hgi, reassoc_of% hmapf, hff', hf₁φ, reassoc_of% hψφ]
    · have w1 : ((Over.pullback FinalForm.u₀).map f₁).left ≫ ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom =
          ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom := Over.w _
      have w2 : ψ ≫ ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom = A'.A.hom ≫ ξ₀ := hψs
      simp only [Category.assoc, w1, w2]
      rw [← Category.assoc, Over.w]
  rw [← Category.assoc, key, Category.assoc, hmapf₁, Category.assoc]

end GlobalTheory.Poinc.Eq8.PullAlong

end
end
