import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelCoverField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenOfIsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitiveOfLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem levelMaps_of_parts : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∃ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → IsFinite rF ∧ Etale rF ∧ Surjective rF) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) := by
  intro h₁ h₂ h₃ h₄ E _ _ _ H D hpq l l₂ Xo Xo₂ hd
  obtain ⟨r, jK, m, hh⟩ := h₁ E H D l l₂ Xo Xo₂ hpq hd
  refine ⟨r, jK, m, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, h₂ E H D l l₂ Xo Xo₂ hpq hd r jK m hh, ?_⟩
  intro c c₂ hc
  have hring : (IntermediateField.inclusion c₂.le).toRingHom.comp jK =
      (IntermediateField.inclusion hc.le).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom := by
    ext x
    exact hh.1 x
  have w : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc.le).toRingHom) ≫
        spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hh.2.1, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
  have e₁ := pullback.lift_fst _ _ w
  have e₂ := pullback.lift_snd _ _ w
  have k₃ := h₃ E H D l l₂ Xo Xo₂ hpq hd r jK m hh c c₂ hc _ e₁ e₂
  exact ⟨pullback.lift _ _ w, e₁, e₂, k₃.1, k₃.2.1, k₃.2.2,
    h₄ E H D l l₂ Xo Xo₂ hpq hd r jK m hh c c₂ hc _ e₁ e₂⟩

end GlobalTheory
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.LevelCover

namespace GlobalTheory.LevCover

private theorem levStrRep_lemma (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [Field B] {b : Base l B} {S : Scheme.{0}} [IsLocallyNoetherian S]
    {s : S ⟶ Sp B} (o : Obj D l b s) (hpq : 1 ≤ D.p + D.q) (l₂ : Level H) (b₂ : Base l₂ B) (hd : l.Dvd l₂)
    (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) :
    ∃ (V : Over S) (χ θ : D.La → (V ⟶ o.t.G)), IsFinite V.hom ∧ Etale V.hom ∧ Surjective V.hom ∧
      LevStr o b₂ V χ θ ∧
      (∀ (T : Over S) (u u' : T ⟶ V), (∀ a, u ≫ χ a = u' ≫ χ a) → (∀ a, u ≫ θ a = u' ≫ θ a) → u = u') ∧
      ∀ (T : Over S) (χ' θ' : D.La → (T ⟶ o.t.G)), LevStr o b₂ T χ' θ' →
        ∃ h : T ⟶ V, (∀ a, h ≫ χ a = χ' a) ∧ ∀ a, h ≫ θ a = θ' a := by
  have hsim := SimAlg.sim_group E H D hpq
  obtain ⟨hfree, hfin⟩ := datum_free D
  refine exists_levStr_rep o l₂ b₂ hd hζ (fun g n k hn hk => hsim.1 g n k hn hk)
    (fun N f ν => exists_sim_lift E H D N f ν)
    (fun l' N ν => SimMult.exists_sim_trivial_of_mult SimAlg.sim_group exists_sim_lift E H D l' N ν) ?_ ?_
  · intro n hn
    have hu : IsUnit ((n : ℕ) : Γ(S, ⊤)) := by
      simpa using (b.unit n hn).map (fnOn s)
    obtain ⟨Z, et, hZ⟩ :=
      exists_finiteEtale_latticeTorsionHom S o.t.G n D.La (ObjDim.isAbelianScheme o) hu
    exact ⟨Z, et, hZ⟩
  · intro N _ T x y c hN hx hy hc
    exact PairingLocus.exists_clopen_of_isLocallyNoetherian hL S (GlobalTheory.Obj.toPolAV o) N T x y c hN hx hy hc

private theorem weilIs_iff_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (T' : Over S') (k : ℤ) (x y : T' ⟶ t'.G)
    (x₀ y₀ : Over.mk (T'.hom ≫ f) ⟶ t.G) (c : Γ(T'.left, ⊤)ˣ) (h₁ : x₀.left = x.left ≫ m.φ)
    (h₂ : y₀.left = y.left ≫ m.φ) : Out.WeilIs t'.G t'.PP.L k x y c ↔ Out.WeilIs t.G t.PP.L k x₀ y₀ c :=
  weilIs_grpPullback_of_comm S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart (sabMap_lbIso m)
    T' k x y x₀ y₀ c h₁ h₂

private theorem lieMult_iff_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (k : Type) [Field k] (x : Sp k ⟶ S')
    (τ : 𝓞 E →+* k) (n : ℕ) : LieMult t'.act x τ n ↔ LieMult t.act (x ≫ f) τ n :=
  LiePull.lieMult_pull (𝓞 E) S S' t.G t'.G f m.φ t.act t'.act m.cart m.act k x τ n

theorem levelCover_noetherian (hL : Out.Laws) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsLocallyNoetherian S → 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ := by
  intro E _ _ _ H D l l₂ B _ b b₂ S s o hS hpq hd hρ hζ
  have := hS
  obtain ⟨V, χ, θ, hVf, hVe, hVs, hlev, hext, hex⟩ := levStrRep_lemma hL o hpq l₂ b₂ hd hζ
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l B B b b (RingHom.id B) S V.left s (V.hom ≫ s) V.hom rfl rfl
    (by rw [spMap_id', Category.comp_id]) o
  obtain ⟨o₂, m, hm, hχ, hθ⟩ := obj_of_levStr o hρ V o₁.t n₁.toSABMap (weilIs_iff_of_sabMap n₁.toSABMap)
    (fun k _ x τ n => lieMult_iff_of_sabMap n₁.toSABMap k x τ n) o₁.ample o₁.ktriv hlev
  refine ⟨V.left, V.hom, o₂, m, hVf, hVe, hVs, hm, ?_⟩
  intro T f o' m' hc
  obtain ⟨χ', θ', hlev', hχ', hθ'⟩ := levStr_of_obj o (Over.mk f) o' m' (weilIs_iff_of_sabMap m') hc.1 hc.2
  obtain ⟨g, hgχ, hgθ⟩ := hex (Over.mk f) χ' θ' hlev'
  have hg : g.left ≫ V.hom = f := by simpa using Over.w g
  obtain ⟨u, hu⟩ := sab_cancel m m' g.left hg

  have key : ∀ a, ((o'.eta a).left ≫ m'.φ = g.left ≫ (o₂.eta a).left ≫ m.φ) ∧
      ((o'.etaA a).left ≫ m'.φ = g.left ≫ (o₂.etaA a).left ≫ m.φ) := fun a => by
    constructor
    · rw [← hχ' a, ← hgχ a, Over.comp_left, hχ a]
    · rw [← hθ' a, ← hgθ a, Over.comp_left, hθ a]
  have hη : ∀ a, (o'.eta a).left ≫ u.φ = g.left ≫ (o₂.eta a).left := fun a =>
    sec_cancel u m (o'.eta a) (o₂.eta a) (by rw [hu]; exact (key a).1)
  have hηA : ∀ a, (o'.etaA a).left ≫ u.φ = g.left ≫ (o₂.etaA a).left := fun a =>
    sec_cancel u m (o'.etaA a) (o₂.etaA a) (by rw [hu]; exact (key a).2)
  refine ⟨g.left, ⟨hg, ⟨u, hη, hηA⟩, hu⟩, ?_⟩
  rintro h' ⟨hh', ⟨u', hu₁, hu₂⟩, hu'⟩
  have hu'' : u'.cm.F ≫ m.φ = m'.φ := hu'
  have hgg : (Over.homMk h' hh' : Over.mk f ⟶ V) = g := by
    apply hext
    · intro a
      ext1
      simp only [Over.comp_left, hχ a, Over.homMk_left]
      rw [← (key a).1, ← Category.assoc, ← hu₁ a, Category.assoc, hu'']
    · intro a
      ext1
      simp only [Over.comp_left, hθ a, Over.homMk_left]
      rw [← (key a).2, ← Category.assoc, ← hu₂ a, Category.assoc, hu'']
  rw [← hgg]
  rfl

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem levelMap_over_field_noetherian (hL : Out.Laws)
    (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X)
    (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm₁ : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (hm₂ : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (F : Type) [Field F] (b : Base l F) (b₂ : Base l₂ F) (j : KA l →+* F) (j₂ : KA l₂ →+* F)
    (e₁ : j (baseKA l).ρ = b.ρ) (e₂ : j (baseKA l).ζ = b.ζ) (e₃ : j₂ (baseKA l₂).ρ = b₂.ρ)
    (e₄ : j₂ (baseKA l₂).ζ = b₂.ζ) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A))
    (rF : pullback Xo₂.s (spMap j₂) ⟶ pullback Xo.s (spMap j))
    (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r) (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) :
    IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  have hsm0 : Smooth Xo.s := by
    have := Xo.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hsm0₂ : Smooth Xo₂.s := by
    have := Xo₂.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo₂.s
  have hsmX : Smooth (pullback.snd Xo.s (spMap j)) := inferInstance
  have hsmX₂ : Smooth (pullback.snd Xo₂.s (spMap j₂)) := inferInstance
  obtain ⟨rX, -, nX⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmX
  obtain ⟨rX₂, -, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmX₂

  obtain ⟨o, ⟨no⟩⟩ := obj_pull E H D l (KA l) F (baseKA l) b j Xo.X (pullback Xo.s (spMap j)) Xo.s
    (pullback.snd _ _) (pullback.fst _ _) e₁ e₂ pullback.condition Xo.univ
  obtain ⟨o₂, ⟨no₂⟩⟩ := obj_pull E H D l₂ (KA l₂) F (baseKA l₂) b₂ j₂ Xo₂.X (pullback Xo₂.s (spMap j₂)) Xo₂.s
    (rF ≫ pullback.snd _ _) (pullback.fst _ _) e₃ e₄ (by rw [h₂]; exact pullback.condition) Xo₂.univ
  have hno1 : ∀ a, (o.eta a).left ≫ no.toSABMap.φ = pullback.fst _ _ ≫ (Xo.univ.eta a).left := no.2
  have hno2 : ∀ a, (o.etaA a).left ≫ no.toSABMap.φ = pullback.fst _ _ ≫ (Xo.univ.etaA a).left := no.3
  have hno₂1 : ∀ a, (o₂.eta a).left ≫ no₂.toSABMap.φ = pullback.fst _ _ ≫ (Xo₂.univ.eta a).left := no₂.2
  have hno₂2 : ∀ a, (o₂.etaA a).left ≫ no₂.toSABMap.φ = pullback.fst _ _ ≫ (Xo₂.univ.etaA a).left := no₂.3
  have hRX : Represents o := represents_pullback ObjMaps.id_comp_cancel Xo j
    (fun S s o' hS => moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo F b j S s o' hS e₁ e₂) rfl o no
  have hRX₂ : Represents o₂ := represents_pullback ObjMaps.id_comp_cancel Xo₂ j₂
    (fun S s o' hS => moduli_rep_of_base ObjMaps.id_comp_cancel E H D l₂ Xo₂ F b₂ j₂ S s o' hS e₃ e₄) h₂ o₂ no₂

  obtain ⟨Y, π, oc, mc, hπf, hπe, hπs, hmc, huniv⟩ :=
    levelCover_noetherian hL E H D l l₂ F b b₂ _ (pullback.snd Xo.s (spMap j)) o nX hpq hd hρ hζ
  have hsmπ : Smooth π := inferInstance
  have hsmY : Smooth (π ≫ pullback.snd Xo.s (spMap j)) := inferInstance
  obtain ⟨rY, -, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmY
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l F F b b (RingHom.id F) _ Y (pullback.snd _ _) (π ≫ pullback.snd _ _) π
    rfl rfl (by rw [spMap_id', Category.comp_id]) o

  obtain ⟨mcomp, hmcomp⟩ := sab_comp no₂.toSABMap m h₁.symm
  obtain ⟨m₂, hm₂'⟩ := sab_cancel no.toSABMap mcomp rF rfl
  have hm₂c : (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m₂.φ = rF ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m₂.φ = rF ≫ (o.etaA a).left) := by
    constructor
    · intro a
      apply sec_cancel m₂ no.toSABMap
      rw [hm₂', hmcomp, ← Category.assoc, sec_pow _ _ _ (hno₂1 a), Category.assoc, hm₁ a, ← Category.assoc,
        ← h₁, Category.assoc, hno1 a]
    · intro a
      apply sec_cancel m₂ no.toSABMap
      rw [hm₂', hmcomp, ← Category.assoc, sec_pow _ _ _ (hno₂2 a), Category.assoc, hm₂ a, ← Category.assoc,
        ← h₁, Category.assoc, hno2 a]
  obtain ⟨h, hiso, hπ⟩ := iso_cover ObjMaps.id_comp_cancel (l₂.M / l.M) (l₂.A / l.A) o o₂ oc o₁ n₁ m₂ mc hm₂c hmc
    hRX hRX₂ rX₂ rY (obj_rigid_closed hL E H D l F F b b _ Y (pullback.snd _ _) (π ≫ pullback.snd _ _) o o₁ π
      (Or.inl rY)) huniv
  rw [← hπ]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end

theorem levelMap_finite_etale_surjective_of_laws (hL : Out.Laws) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  intro E _ _ _ H D l l₂ Xo Xo₂ hpq hd r jK m hr c c₂ hc rF h₁ h₂
  obtain ⟨-, -, hm₁, hm₂⟩ := hr
  obtain ⟨F, fin, conj, zm, le⟩ := c
  obtain ⟨F₂, fin₂, conj₂, zm₂, le₂⟩ := c₂
  dsimp only at hc
  subst hc
  rw [spMap_inclusion_self, Category.comp_id] at h₂
  exact levelMap_over_field_noetherian hL Xo Xo₂ hpq hd r m hm₁ hm₂ F (baseOf l F le) (baseOf l₂ F le₂)
    (IntermediateField.inclusion le).toRingHom (IntermediateField.inclusion le₂).toRingHom rfl rfl rfl rfl
    (baseOf_rho l l₂ F le le₂) (baseOf_zeta l l₂ F le le₂ hd.2.2) rF h₁ h₂

end GlobalTheory.LevCover
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.levelMap_fibre_orbit : Out.Laws → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing
    B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s'
    : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
    : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b'
    : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s''
    : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
    : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
    : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
    f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
    f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B
    : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂
    : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m
    : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta
    a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s
    : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S'
    ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta
    a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B
    : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k : Type) [Field
    k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e
    : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : TateIso D k Q act e, ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f
    n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n
    : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n
    : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f
    n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo
    : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK
    : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l)
    : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA
    a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo
    : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK
    : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l)
    : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc
    : c.F = c₂.F) (rF
    : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion
    hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y'
    : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ
    : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g
    : Sim D) (ρ
    : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂ :=
  GlobalTheory.LevelFibre.levelMap_fibre_simply_transitive_of_laws
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem levelMaps_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) := by
  intro hL

  have hsm := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
  have hid := ObjMaps.id_comp_cancel
  have hlow := obj_lower_level
  have hrep := moduli_rep_of_base hid
  have hsim := SimAlg.sim_group
  have hact := Moduli.LevelAction.similitude_acts hsm hid hlow hrep
    (exists_obj_twist_by_similitude hsim) hsim
  exact levelMaps_of_parts (exists_levelMap hsm hid hlow hrep) hact
    (LevCover.levelMap_finite_etale_surjective_of_laws hL)
    (levelMap_fibre_orbit hL obj_pull hid obj_isAbelianScheme_dim_rigidified_sym hlow
      (obj_rigid_closed hL) hrep tateIso_differ_by_similitude hsim hact)

end GlobalTheory
end
