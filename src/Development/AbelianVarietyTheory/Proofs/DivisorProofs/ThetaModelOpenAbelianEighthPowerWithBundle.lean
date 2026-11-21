import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEighthPowerGroupPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperEighthFibrePowerOver

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighth_power_universal_object_at_model_stalk : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ z : V.toScheme, ∃ (cO : SiegPre g n ζ ((V.toScheme.fromSpecStalk z ≫ v) ≫ F.s)) (prO : Fin 8 → ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G ⟶ cO.A)), SiegPB cO F.univ (V.toScheme.fromSpecStalk z ≫ v) ∧ (∀ a, IsMonHom (prO a)) ∧ (∀ (T' : Over (Spec (V.toScheme.presheaf.stalk z))) (y : Fin 8 → (T' ⟶ cO.A)), ∃! x : T' ⟶ (Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G, ∀ a, x ≫ prO a = y a) ∧ LBIso (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (V.toScheme.fromSpecStalk z ≫ V.ι))) (LB.LinComb cO.P (K := Fin 8 × Fin 8) (fun ab => (lift (prO ab.1) (prO ab.2)).left) (fun ab => W ab.1 ab.2)) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G), MatOn FinalForm pr a b f → MatEnd prO a b ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).map f) := by
  first | exact @GlobalTheory.Poinc.Eq8.StalkPow.eighth_power_at_stalk | exact GlobalTheory.Poinc.Eq8.StalkPow.eighth_power_at_stalk | (intros; apply GlobalTheory.Poinc.Eq8.StalkPow.eighth_power_at_stalk <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.FieldPt

theorem of_factor {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {C : Over (Sp S.R)} [GrpObj C] (pr : Fin 8 → (ρ.P.A ⟶ C))
    (V : M.Z.Opens) (v : V.toScheme ⟶ F.X) {T₀ : Scheme.{0}} (ξ : T₀ ⟶ V.toScheme)
    (cO : SiegPre g n ζ ((ξ ≫ v) ≫ F.s)) (prO : Fin 8 → ((Over.pullback (ξ ≫ V.ι)).obj FinalForm.G ⟶ cO.A))
    (hpbO : SiegPB cO F.univ (ξ ≫ v)) (hmonO : ∀ a, IsMonHom (prO a))
    (hunivO : ∀ (T' : Over T₀) (y : Fin 8 → (T' ⟶ cO.A)), ∃! x : T' ⟶ (Over.pullback (ξ ≫ V.ι)).obj FinalForm.G,
      ∀ a, x ≫ prO a = y a)
    (hLO : LBIso (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι)))
      (LB.LinComb cO.P (K := Fin 8 × Fin 8) (fun ab => (lift (prO ab.1) (prO ab.2)).left) (fun ab => W ab.1 ab.2)))
    (hmatO : ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G), MatOn FinalForm pr a b f → MatEnd prO a b ((Over.pullback (ξ ≫ V.ι)).map f))
    {K : Type} [Field K] (t : Sp K ⟶ V.toScheme) (t' : Sp K ⟶ T₀) (ht : t' ≫ ξ = t)
    (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left) (hB : IsGrpPullback B FinalForm.G (t ≫ V.ι) φB) :
    ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧
      (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧
      (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8)
        (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧
      ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left →
        MatEnd pr' a b fB := by
  subst ht
  have hB' : IsGrpPullback B FinalForm.G (t' ≫ (ξ ≫ V.ι)) φB := hB.congr (Category.assoc _ _ _) rfl
  have hφ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (ξ ≫ V.ι) t' hB'
  have hφ'f : pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) ≫ pullback.fst FinalForm.G.hom (ξ ≫ V.ι) = φB :=
    pullback.lift_fst _ _ _
  have hφ's : pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) ≫ pullback.snd FinalForm.G.hom (ξ ≫ V.ι) =
      B.hom ≫ t' := pullback.lift_snd _ _ _
  generalize pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) = φ' at hφ hφ'f hφ's
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n o o ζ ζ (RingHom.id o) _ (Sp K)
    ((ξ ≫ v) ≫ F.s) (((t' ≫ ξ) ≫ v) ≫ F.s) t' rfl (by rw [hid, Category.comp_id]; simp only [Category.assoc])).1 cO
  have hcomp := GlobalTheory.SiegelPullComp.pb_comp hpbO hc'
  rw [← Category.assoc] at hcomp
  obtain ⟨χ, χ₂, hχ, hsq, hP, -⟩ := hc'
  obtain ⟨pr', hpr', hmon', huniv'⟩ := GlobalTheory.GrpPullPow.pr_pull prO hφ hχ hmonO hunivO
  refine ⟨c', pr', hcomp, hmon', huniv', ?_, ?_⟩
  · intro L' hL' hiso
    have hL := FinalForm.L.isLB
    have e1 : LBIso (FinalForm.L.L.pull φB) ((FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι))).pull φ') := by
      rw [← hφ'f]
      exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame FinalForm.L.L _ _ _ φ' fun _ => rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι))) φ' φ' rfl)
        ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso _, ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen (pull_isLB hL _)⟩
    have e2 := LBIso.trans hL' (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) hiso e1
    exact GlobalTheory.Poinc.Eq8.lbIso_eighth_pull cO.P c'.P _ L' prO pr' W cO.isLB c'.isLB (pull_isLB hL _) hL' hsq hP hpr'
      e2 hLO
  · intro a b f fB hf hfB
    refine GlobalTheory.MatEndPull.matEnd_pull prO pr' a b _ fB hφ hχ hpr' ?_ (hmatO a b f hf)
    apply pullback.hom_ext
    · have e : ((Over.pullback (ξ ≫ V.ι)).map f).left ≫ pullback.fst FinalForm.G.hom (ξ ≫ V.ι) =
          pullback.fst FinalForm.G.hom (ξ ≫ V.ι) ≫ f.left := pullback.lift_fst _ _ _
      rw [Category.assoc, Category.assoc, hφ'f, e, ← Category.assoc, hφ'f, hfB]
    · have w1 : ((Over.pullback (ξ ≫ V.ι)).map f).left ≫ pullback.snd FinalForm.G.hom (ξ ≫ V.ι) =
          pullback.snd FinalForm.G.hom (ξ ≫ V.ι) := pullback.lift_snd _ _ _
      rw [Category.assoc, Category.assoc, hφ's, w1, hφ's, ← Category.assoc, Over.w fB]

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (K : Type) [Field K] (t : Sp K ⟶ V.toScheme) (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left), IsGrpPullback B FinalForm.G (t ≫ V.ι) φB → ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧ (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧ (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left → MatEnd pr' a b fB := by
  intro g n o _ ζ F W o' Ω _ _ _ _ S ρ u c pr hS M U₀ EE FinalForm hO V v hv K _ t B _ φB hB
  obtain ⟨cO, prO, hpbO, hmonO, hunivO, hLO, hmatO⟩ := GlobalTheory.T.eighth_power_universal_object_at_model_stalk g n o ζ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm hO V v hv
    (t (IsLocalRing.closedPoint K))
  exact of_factor F W FinalForm pr V v _ cO prO hpbO hmonO hunivO hLO hmatO t _
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk t) B φB hB

end GlobalTheory.Poinc.Eq8.FieldPt

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_fieldPoint_eq_eighthPower_universal_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (K : Type) [Field K] (t : Sp K ⟶ V.toScheme) (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left), IsGrpPullback B FinalForm.G (t ≫ V.ι) φB → ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧ (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧ (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left → MatEnd pr' a b fB := by
  atlas_forward_decl GlobalTheory.Poinc.Eq8.FieldPt.main
end

section
open AlgebraicGeometry CategoryTheory Limits

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_eighth_fibre_power_over : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)), (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) → IsProper C.hom → IsProper B.hom := by
  first | exact @GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power | exact GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power | (intros; apply GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.SharpOnV

theorem lAb : ∀ {X : Scheme.{0}} (G : Over X) (V : X.Opens), (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ V.toScheme), IsProper (pullback.snd G.hom (t ≫ V.ι))) → (V : Set X) ⊆ abLocus G := by
  intro X G V h s hs K _ _ t ⟨p, hp⟩
  have hr : Set.range t.base ⊆ (V : Set X) := by
    rintro _ ⟨q, rfl⟩
    have : q = p := Subsingleton.elim _ _
    subst this
    rw [hp]; exact hs
  let t' := IsOpenImmersion.lift V.ι t (by rwa [Scheme.Opens.range_ι])
  have ht : t' ≫ V.ι = t := IsOpenImmersion.lift_fac _ _ _
  have := h K t'
  rwa [ht] at this

theorem lGen : ∀ {X : Scheme.{0}} {G : Over X} [GrpObj G] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ X) (gm : G'.left ⟶ G.left), IsGrpPullback G' G ξ gm → IsGrpPullback A'.A G (jK R ≫ ξ) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) := by
  intro X G _ R _ _ _ G' _ _ D' A' U' ξ gm hgm
  exact ((GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK R) G' U'.gen U'.gen_hom).comp hgm).congr rfl (Category.assoc _ _ _)

theorem lLB : ∀ {X : Scheme.{0}} (L : LB X) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ X), L.IsLB → LBIso U'.LG.L (L.pull gm) → LBIso A'.L (L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm)) := by
  intro X L R _ _ _ G' _ _ D' A' U' gm hL hLB
  have hA := A'.isLB
  have ext : LBIso (A'.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G'.hom (jK R))) := U'.ext
  have H1 := GlobalTheory.ThetaAffineGlue.lbIso_comp (pull_isLB hA _) U'.LG.isLB hL ext hLB
  have H2 := GlobalTheory.ThetaAffineGlue.lbIso_pull H1 U'.gen.inv.left
  have hP : (A'.L.pull U'.gen.hom.left).IsLB := pull_isLB hA _
  have refl : LBIso (A'.L.pull U'.gen.hom.left) (A'.L.pull U'.gen.hom.left) :=
    LBIso.trans hP (pull_isLB hP _) hP (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP) (LBIso.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP))
  have H4 := GlobalTheory.ThetaAffineGlue.lbIso_pull refl U'.gen.inv.left
  have e : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  rw [e] at H4
  have H3 : LBIso A'.L ((A'.L.pull U'.gen.hom.left).pull U'.gen.inv.left) :=
    LBIso.trans hA (pull_isLB hA _) (pull_isLB hP _) (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hA) (LBIso.symm H4)
  exact LBIso.trans hA (pull_isLB hP _) (pull_isLB hL _) H3 H2

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → (V : Set M.Z) ⊆ abLocus FinalForm.G ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → ∀ ξ₀ : Sp (FractionRing R) ⟶ V.toScheme, ξ₀ ≫ V.ι = jK R ≫ ξ → ∃ c' pr', SharpBy F W A' (ξ₀ ≫ v) c' pr' ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (f' : G' ⟶ G'), MatOn FinalForm pr a b f → f'.left ≫ gm = gm ≫ f.left → ∃ f₁ : A'.A ⟶ A'.A, MatEnd pr' a b f₁ ∧ (Over.pullback (jK R)).map f' ≫ U'.gen.hom = U'.gen.hom ≫ f₁ := by
  intro g n o _ ζ F W o' Ω _ _ _ _ S ρ u c pr hS M U₀ EE FinalForm hO V v hv
  have hK := GlobalTheory.T.semiAbelian_fieldPoint_eq_eighthPower_universal_pullback g n o ζ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm hO V v hv
  refine ⟨lAb FinalForm.G V fun K _ _ t => ?_, ?_⟩
  · obtain ⟨c', pr', -, -, huniv, -, -⟩ := hK K t ((Over.pullback (t ≫ V.ι)).obj FinalForm.G) (pullback.fst _ _)
      (isGrpPullback_pullback _ _)
    exact GlobalTheory.T.isProper_eighth_fibre_power_over pr' huniv c'.ab.proper
  · intro R _ _ _ hB G' _ _ hsemi D' A' U' ξ gm hgm hLB ξ₀ hξ₀
    have hpb : IsGrpPullback A'.A FinalForm.G (ξ₀ ≫ V.ι) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) :=
      (lGen U' ξ gm hgm).congr hξ₀.symm rfl
    have hL := lLB FinalForm.L.L U' gm FinalForm.L.isLB hLB
    obtain ⟨c', pr', hSP, hmon, huniv, hlb, hmat⟩ := hK (FractionRing R) ξ₀ A'.A _ hpb
    refine ⟨c', pr', ⟨hSP, hmon, huniv, hlb A'.L A'.isLB hL⟩, fun a b f f' hf hff' => ?_⟩
    have hgi : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    have hmapf : ((Over.pullback (jK R)).map f').left ≫ pullback.fst G'.hom (jK R) = pullback.fst G'.hom (jK R) ≫ f'.left :=
      pullback.lift_fst _ _ _
    refine ⟨U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom, hmat a b f _ hf ?_, by simp⟩
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% hgi, reassoc_of% hmapf, hff']

end GlobalTheory.Poinc.Eq8.SharpOnV

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModel_open_abelian_eighthPower_with_bundle : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → (V : Set M.Z) ⊆ abLocus FinalForm.G ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → ∀ ξ₀ : Sp (FractionRing R) ⟶ V.toScheme, ξ₀ ≫ V.ι = jK R ≫ ξ → ∃ c' pr', SharpBy F W A' (ξ₀ ≫ v) c' pr' ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (f' : G' ⟶ G'), MatOn FinalForm pr a b f → f'.left ≫ gm = gm ≫ f.left → ∃ f₁ : A'.A ⟶ A'.A, MatEnd pr' a b f₁ ∧ (Over.pullback (jK R)).map f' ≫ U'.gen.hom = U'.gen.hom ≫ f₁ := by
  atlas_forward_decl GlobalTheory.Poinc.Eq8.SharpOnV.main
end
