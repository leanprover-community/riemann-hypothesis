import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingUniversalProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPeriodRingSeparation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrToContInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSpanIffOfBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsQuot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExtensionLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GammaComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemMapBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepDesc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentRefinementOfUnimodular
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationUniversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrTeichProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IncPtInjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FibInit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FRiCalc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainDegreeZeroSubsingleton
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompShiftZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmpPutSucc
import BuildAid.D2

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.eps_facts : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) :=
  @GlobalTheory.CompanionTheory.EpsFacts.eps_facts

theorem CrystallineSemistableComparison.B.P.cont_line : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), ∃ L : Line (jE (F.pt κ)) (epsU ε (F.pt κ)), ∀ T, ((flt F κ ε k n ρ hρ).comap (gE F κ k n)).FAcyc (L.i.app T) (L.γ.app T) :=
  @GlobalTheory.CompanionTheory.ContLine.exists_line

theorem CrystallineSemistableComparison.B.P.tower_ex : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} (κ : O →+* OC l) {d : ℕ} (s : F.Small d), Nonempty (Tower κ s) :=
  @GlobalTheory.CompanionTheory.TowerEx.tower_ex

theorem CrystallineSemistableComparison.B.P.tower_act : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (ε : Eps l), ∃ A : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj, ∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d), PAlg.Hom.f (A.act a φ).1 (𝒯.c k 0).val = ((a k).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c k 0).val :=
  @GlobalTheory.CompanionTheory.TowerAct.tower_act

theorem CrystallineSemistableComparison.B.P.theta_ex : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (ε : Eps l) (A : Act (𝟭 _) (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)) d (liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)) (A' : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj), (∀ (T : Thick (Lc F κ k n)) (a : Fin d → (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)).U T) (c : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ T) (j : Fin d), (A.act a c).φ (𝓛.t j) = ((a j).1 : T.B) * c.φ (𝓛.t j)) → (∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (j : Fin d), PAlg.Hom.f (A'.act a φ).1 (𝒯.c j 0).val = ((a j).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c j 0).val) → ∃ θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj, (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) ∧ ∀ a, (A.γ a : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn) ≫ θ = θ ≫ (gE F κ k n).map (A'.γ a) :=
  @GlobalTheory.CompanionTheory.ThetaEx.main

theorem CrystallineSemistableComparison.B.P.local_ni : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (ε : Eps l) (ρ : ℕ → ℕ) (hρ : Slow ρ) (γ : Gam d →* End (liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)) (γ' : Gam d →* End 𝒯.obj) (θ : SingleObj.functor γ ⟶ SingleObj.functor γ' ⋙ gE F κ k n), n ≠ 0 → (∀ j, (θ.app (SingleObj.star _)).φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) → (∀ a j, Thick.Hom.φ (γ a : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn) (𝓛.t j) = 𝓛.i (ε.qU n) ^ (Multiplicative.toAdd a j) * 𝓛.t j) → (∀ a j, PAlg.Hom.f (A := 𝒯.A) (B := 𝒯.A) (γ' a : 𝒯.obj ⟶ 𝒯.obj).1 (𝒯.c j 0).val = 𝒯.A.s (ε.e 0) ^ (Multiplicative.toAdd a j) * (𝒯.c j 0).val) → Nonempty (NI (Polynomial.X : Polynomial ℤ) (Functor.whiskerRight θ (flt F κ ε k n ρ hρ).rees)) :=
  @GlobalTheory.CompanionTheory.TowerNI.main

theorem CrystallineSemistableComparison.B.P.desc : ∀ {l : ℕ} [Fact l.Prime], D.Out l → ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), (k = false ∨ ρ = 0) → Desc (Polynomial.X : Polynomial ℤ) (gE F κ k n ⋙ (flt F κ ε k n ρ hρ).rees) (jE (F.pt κ)) :=
  @GlobalTheory.CompanionTheory.DescTest.main

theorem CrystallineSemistableComparison.B.P.el_zar : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (k : Bool) (n r : ℕ), ZarCov (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) fun T => ∃ α, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 :=
  @GlobalTheory.CompanionTheory.TestZar.zarCov_test

theorem CrystallineSemistableComparison.B.P.el_onto : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (S : Set 𝒜.A) (k : Bool) (n : ℕ), n ≠ 0 → Onto (subEl κ (Fn.Sub.inter 𝒜.V S)) fun T => ∀ α ∈ S, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 :=
  @GlobalTheory.CompanionTheory.ElOnto.onto_subEl
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section Cm

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {E : Type u''} [Category.{v''} E]
  (j : C' ⥤ C) (ι : E ⥤ C) (e : E)

def cmL : StructuredArrow (ι.obj e) j ⥤ StructuredArrow e (Comma.fst ι j) where
  obj y := StructuredArrow.mk (Y := (⟨e, y.right, y.hom⟩ : Comma ι j)) (𝟙 e)
  map {y y'} f := StructuredArrow.homMk ⟨𝟙 e, f.right, by simp [StructuredArrow.w f]⟩ (by simp)
  map_id y := by ext <;> simp
  map_comp f g := by ext <;> simp

def cmU : StructuredArrow e (Comma.fst ι j) ⥤ StructuredArrow (ι.obj e) j where
  obj x := StructuredArrow.mk (Y := x.right.right) (ι.map x.hom ≫ x.right.hom)
  map {x x'} f := StructuredArrow.homMk f.right.right (by
    have h2 := StructuredArrow.w f
    dsimp at h2 ⊢
    rw [Category.assoc, ← f.right.w, ← Category.assoc, ← ι.map_comp, show x.hom ≫ f.right.left = x'.hom from h2])
  map_id x := by ext; simp
  map_comp f g := by ext; simp

theorem cm_w {y : StructuredArrow (ι.obj e) j} {x : StructuredArrow e (Comma.fst ι j)} (g : (cmL j ι e).obj y ⟶ x) :
    g.right.left = x.hom := by
  have h2 := StructuredArrow.w g
  dsimp [cmL] at h2
  simpa using h2

def cmAdj : cmL j ι e ⊣ cmU j ι e :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun y x =>
        { toFun := fun g => StructuredArrow.homMk g.right.right (by
            dsimp [cmL, cmU]
            rw [← cm_w j ι e g]
            exact g.right.w.symm)
          invFun := fun f => StructuredArrow.homMk
            { left := x.hom, right := f.right, w := (StructuredArrow.w f).symm } (by dsimp [cmL]; simp)
          left_inv := fun g => by
            apply StructuredArrow.ext
            apply Comma.hom_ext
            · exact (cm_w j ι e g).symm
            · rfl
          right_inv := fun f => by
            apply StructuredArrow.ext
            rfl }
      homEquiv_naturality_left_symm := by
        intro y' y x f g
        apply StructuredArrow.ext
        apply Comma.hom_ext
        all_goals (dsimp [cmL]; try simp)
      homEquiv_naturality_right := by
        intro y x x' f g
        apply StructuredArrow.ext
        dsimp [cmU]
        try simp }

end Cm

def cmMor {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {E : Type u''}
    [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C) (e : E) :
    Mor (StructuredArrow.proj e (Comma.fst ι j) ⋙ Comma.snd ι j ⋙ j ⋙ F)
      (StructuredArrow.proj (ι.obj e) j ⋙ j ⋙ F) (RingHom.id R) where
  G := cmL j ι e
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem cm_aug_cocycle {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (T : C) (a : F.obj T) :
    d (StructuredArrow.proj T m.G ⋙ F') 0
      (aug (StructuredArrow.proj T m.G ⋙ F') (fun x => (m.τ x.right) ∘ₗ (F.map x.hom).hom) a) = 0 := by
  rw [← fib_aug m T]
  have := (relMor (𝟭 C) m T).hom.comm 0
    (aug (relF (𝟭 C) F T) (fun T' => ((relF (𝟭 C) F T).map ((fib_init T).to T')).hom) a)
  have h0 := (CrystallineSemistableComparison.P.initial (relF (𝟭 C) F T) _ (fib_init T)).1 a
  exact this.trans ((congrArg _ h0).trans (map_zero _))

theorem cm_transfer {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    (hb : ∀ n, Function.Bijective (φ.mapH n)) {M : Type u''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0)
    (hd : ∀ x, K.d 0 (ε x) = 0) (s : R) (hL : L.ResUpTo s (φ.f 0 ∘ₗ ε)) : K.ResUpTo s ε := by
  have h1 : ∀ n, UpTo (1 : R) (φ.mapH n) := fun n =>
    ((CrystallineSemistableComparison.P.upTo_alg (φ.mapH n) LinearMap.id (1 : R) 1).2.2.2.2).2 (hb n)
  have := (CrystallineSemistableComparison.P.res_transfer φ ε s 1 h1).2 hd hL
  rwa [mul_one] at this

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.comma1 : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {E : Type u''} [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C) (s : R) (h : ∀ {x y : Comma ι j} (φ : x ⟶ y) (a : F.obj (ι.obj x.left)), (F.map y.hom).hom ((F.map (ι.map φ.left)).hom a) = (F.map (j.map φ.right)).hom ((F.map x.hom).hom a)), Desc s F j → ∀ n, IsoLe (s ^ (2 * n + 3)) n (⟨Comma.fst ι j, fun x => (F.map x.hom).hom, fun φ a => h φ a⟩ : Mor (ι ⋙ F) (Comma.snd ι j ⋙ j ⋙ F) (RingHom.id R)) := by
  intro R _ C _ C' _ E _ F j ι s h hD n
  refine CrystallineSemistableComparison.B.P.fib _ s (fun e => ?_) n
  have : (CrystallineSemistableComparison.B.cmMor F j ι e).G.IsLeftAdjoint := (CrystallineSemistableComparison.B.cmAdj j ι e).isLeftAdjoint
  refine CrystallineSemistableComparison.B.cm_transfer (CrystallineSemistableComparison.B.cmMor F j ι e).hom
    (fun k => CrystallineSemistableComparison.P.adj_mor (CrystallineSemistableComparison.B.cmMor F j ι e) (fun _ => Function.bijective_id) k) _
    (CrystallineSemistableComparison.B.cm_aug_cocycle (⟨Comma.fst ι j, fun x => (F.map x.hom).hom, fun φ a => h φ a⟩ : Mor (ι ⋙ F) (Comma.snd ι j ⋙ j ⋙ F) (RingHom.id R)) e) s ?_
  have eq : (CrystallineSemistableComparison.B.cmMor F j ι e).hom.f 0 ∘ₗ
      (aug (StructuredArrow.proj e (Comma.fst ι j) ⋙ Comma.snd ι j ⋙ j ⋙ F)
        fun x => (F.map x.right.hom).hom ∘ₗ ((ι ⋙ F).map x.hom).hom) = unAug F j (ι.obj e) := by
    apply LinearMap.ext; intro a; funext c
    change (F.map (c.obj (Fin.last 0)).hom).hom ((F.map (ι.map (𝟙 e))).hom a) = (F.map (c.obj (Fin.last 0)).hom).hom a
    rw [ι.map_id, F.map_id]
    rfl
  exact eq ▸ hD (ι.obj e)
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

theorem fible_succ {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) (q : ℕ)
    (s₁ s₂ : R) (hK : ExactUpTo s₁ (K.d q) (K.d (q + 1))) (hφ : SurjUpTo s₂ (φ.mapH (q + 1))) :
    ExactUpTo (s₁ * s₂) (L.d q) (L.d (q + 1)) := by
  intro y hy
  obtain ⟨x, hx⟩ := hφ (L.cls y hy)
  obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K (q + 1)).1 x
  obtain ⟨c, hc⟩ := hK b hb
  have hfb : L.d (q + 1) (φ.f (q + 1) b) = 0 := by rw [φ.comm, hb, map_zero]
  have hy2 : L.d (q + 1) (s₂ • y) = 0 := by rw [map_smul, hy, smul_zero]
  have hy12 : L.d (q + 1) (s₁ • s₂ • y) = 0 := by rw [map_smul, hy2, smul_zero]
  have hs1b : L.d (q + 1) (s₁ • φ.f (q + 1) b) = 0 := by rw [map_smul, hfb, smul_zero]
  rw [CrystallineSemistableComparison.P.mapH_cls φ (q + 1) b hb hfb, ← resLe_cls_smul L (q + 1) s₂ y hy hy2] at hx
  have e1 : L.cls (s₁ • s₂ • y) hy12 = L.cls (s₁ • φ.f (q + 1) b) hs1b := by
    rw [resLe_cls_smul L (q + 1) s₁ _ hfb hs1b, hx, ← resLe_cls_smul L (q + 1) s₁ _ hy2 hy12]
  have e2 : L.cls (s₁ • φ.f (q + 1) b) hs1b = 0 := by
    refine resLe_cls_zero L (q + 1) _ hs1b ⟨φ.f q c, ?_⟩
    rw [φ.comm, hc, map_smul]
  rw [e2] at e1
  obtain ⟨c', hc'⟩ := ((CrystallineSemistableComparison.P.cls_surj L (q + 1)).2.1 _ hy12).1 e1
  exact ⟨c', by rw [hc', mul_smul]⟩

theorem fible_zero {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    {A : Type u''} [AddCommGroup A] [Module R A] (ε : A →ₗ[R] K.X 0) (hd : ∀ x, K.d 0 (ε x) = 0) (s₁ s₂ : R)
    (hi : InjUpTo s₁ ε) (he : ExactUpTo s₁ ε (K.d 0)) (hφ : UpTo s₂ (φ.mapH 0)) :
    InjUpTo (s₁ * s₂) (φ.f 0 ∘ₗ ε) ∧ ExactUpTo (s₁ * s₂) (φ.f 0 ∘ₗ ε) (L.d 0) := by
  have hLd : ∀ x, L.d 0 (φ.f 0 (ε x)) = 0 := fun x => by rw [φ.comm, hd, map_zero]
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h1 : φ.mapH 0 (K.cls (ε x) (hd x)) = 0 := by
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 _ _ (hLd x)]
      exact resLe_cls_zero L 0 _ _ (by rw [show φ.f 0 (ε x) = 0 from hx]; exact Submodule.zero_mem _)
    have h2 := hφ.1 _ h1
    have hs' : K.d 0 (s₂ • ε x) = 0 := by rw [map_smul, hd, smul_zero]
    rw [← resLe_cls_smul K 0 s₂ _ _ hs'] at h2
    have h3 : s₂ • ε x = 0 := eq_zero_of_mem_boundaries_zero _ _ (((CrystallineSemistableComparison.P.cls_surj K 0).2.1 _ hs').1 h2)
    rw [← map_smul] at h3
    rw [mul_smul]
    exact hi _ h3
  · obtain ⟨x, hx⟩ := hφ.2 (L.cls y hy)
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 x
    obtain ⟨a, ha⟩ := he b hb
    refine ⟨a, ?_⟩
    have hy' : L.d 0 (s₂ • y) = 0 := by rw [map_smul, hy, smul_zero]
    have hfb : L.d 0 (φ.f 0 b) = 0 := by rw [φ.comm, hb, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls φ 0 b hb hfb, ← resLe_cls_smul L 0 s₂ y hy hy'] at hx
    have := ((CrystallineSemistableComparison.P.cls_surj L 0).2.2.1 _ _ hfb hy').1 hx
    have h4 : φ.f 0 b = s₂ • y := sub_eq_zero.1 (eq_zero_of_mem_boundaries_zero _ _ this)
    change φ.f 0 (ε a) = _
    rw [ha, map_smul, h4, mul_smul]

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.fible : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (s : R) (n : ℕ), (∀ T : C, ∃ (E : Type v'') (_ : Category.{u''} E) (M : E ⥤ ModuleCat.{w} R) (μ : Mor M (StructuredArrow.proj T m.G ⋙ F') (RingHom.id R)) (e : ∀ x : E, F.obj T →ₗ[R] M.obj x) (s₁ s₂ : R), s = s₁ * s₂ ∧ (∀ x a, μ.τ x (e _ a) = m.τ x.right ((F.map x.hom).hom a)) ∧ (∀ (x y : E) (φ : x ⟶ y) a, (M.map φ).hom (e x a) = e y a) ∧ IsoLe s₂ (n + 1) μ ∧ InjUpTo s₁ (aug M e) ∧ ExactUpTo s₁ (aug M e) (d M 0) ∧ ∀ j ≤ n, ExactUpTo s₁ (d M j) (d M (j + 1))) → IsoLe (s ^ (2 * n + 3)) n m := by
  intro R _ C _ C' _ F F' m s n hT
  have key : ∀ (T : C), ∀ q ≤ n + 1, UpTo s ((relMor (𝟭 C) m T).pull q) := by
    intro T q hq
    obtain ⟨E, _, M, μ, e, s₁, s₂, rfl, hμe, he, hiso, hinj, hex0, hex⟩ := hT T
    have hK := CrystallineSemistableComparison.P.initial (relF (𝟭 C) F T) _ (fib_init T)
    cases q with
    | zero =>
      refine (resLe_zero (relMor (𝟭 C) m T).hom _ hK _).2 ?_
      have hd : ∀ a, d M 0 (aug M e a) = 0 := by
        intro a; funext c
        change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (M.map (GlobalTheory.CatH.toLast i c)).hom (e _ a) = 0
        simp only [he, Fin.sum_univ_two]
        simp
      have eqε : (relMor (𝟭 C) m T).hom.f 0 ∘ₗ
          aug (relF (𝟭 C) F T) (fun x => ((relF (𝟭 C) F T).map ((fib_init T).to x)).hom) =
          μ.hom.f 0 ∘ₗ aug M e := by
        have e1 : (relMor (𝟭 C) m T).hom.f 0 ∘ₗ
            aug (relF (𝟭 C) F T) (fun x => ((relF (𝟭 C) F T).map ((fib_init T).to x)).hom) =
            aug (relF (m.G ⋙ 𝟭 C) F' T) fun x => ((relMor (𝟭 C) m T).τ x) ∘ₗ
              ((relF (𝟭 C) F T).map ((fib_init T).to ((relMor (𝟭 C) m T).G.obj x))).hom :=
          LinearMap.ext fun a => funext fun c => rfl
        rw [e1, fib_aug]
        apply LinearMap.ext; intro a; funext c
        exact (hμe _ a).symm
      rw [eqε]
      exact fible_zero μ.hom (aug M e) hd s₁ s₂ hinj hex0 (hiso 0 (Nat.zero_le _))
    | succ q =>
      refine (resLe_succ (relMor (𝟭 C) m T).hom q (hK.2.2.2 q) _).2 ?_
      exact fible_succ μ.hom q s₁ s₂ (hex q (by omega)) (hiso (q + 1) (by omega)).2
  intro j hj
  have h1 := CrystallineSemistableComparison.P.rel (𝟭 C) m s j (fun i q hq => key i q (by omega))
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
  have e : s ^ (2 * (j + k) + 3) = s ^ (2 * j + 3) * s ^ (2 * k) := by rw [← pow_add]; ring_nf
  rw [e]
  exact (CrystallineSemistableComparison.P.upTo_alg (m.pull j) LinearMap.id _ _).2.2.2.1 h1
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section gam

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

theorem gam_h {E : Type u''} [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C)
    {x y : Comma ι j} (φ : x ⟶ y) (a : F.obj (ι.obj x.left)) :
    (F.map y.hom).hom ((F.map (ι.map φ.left)).hom a) = (F.map (j.map φ.right)).hom ((F.map x.hom).hom a) := by
  rw [← ModuleCat.comp_apply, ← F.map_comp, ← ModuleCat.comp_apply, ← F.map_comp, φ.w]

def gamCm {E : Type u''} [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C) :
    Mor (ι ⋙ F) (Comma.snd ι j ⋙ j ⋙ F) (RingHom.id R) :=
  ⟨Comma.fst ι j, fun x => (F.map x.hom).hom, fun φ a => gam_h F j ι φ a⟩

structure GamDat {Γ : Type} [CommMonoid Γ] {D : C} (γ : Γ →* End D) (j : C' ⥤ C) (t : C') where
  S : C
  il : D ⟶ S
  ir : j.obj t ⟶ S
  g : Γ →* End S
  hil : ∀ a, il ≫ (g a : S ⟶ S) = (γ a : D ⟶ D) ≫ il
  hir : ∀ a, ir ≫ (g a : S ⟶ S) = ir
  hu : ∀ (t' : C') (c : D ⟶ j.obj t') (φ : j.obj t ⟶ j.obj t'), ∃! ψ : S ⟶ j.obj t', il ≫ ψ = c ∧ ir ≫ ψ = φ

namespace GamDat

variable {Γ : Type} [CommMonoid Γ] {D : C} {γ : Γ →* End D} {j : C' ⥤ C} {t : C'} (P : GamDat γ j t)

theorem uniq {t' : C'} (ψ ψ' : P.S ⟶ j.obj t') (h1 : P.il ≫ ψ = P.il ≫ ψ') (h2 : P.ir ≫ ψ = P.ir ≫ ψ') : ψ = ψ' :=
  (P.hu t' _ _).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩

noncomputable def ψ (x : StructuredArrow t (Comma.snd (SingleObj.functor γ) j)) : P.S ⟶ j.obj x.right.right :=
  (P.hu x.right.right x.right.hom (j.map x.hom)).exists.choose

theorem ψ_spec (x : StructuredArrow t (Comma.snd (SingleObj.functor γ) j)) :
    P.il ≫ P.ψ x = x.right.hom ∧ P.ir ≫ P.ψ x = j.map x.hom :=
  (P.hu x.right.right x.right.hom (j.map x.hom)).exists.choose_spec

theorem ψ_nat {x y : StructuredArrow t (Comma.snd (SingleObj.functor γ) j)} (f : x ⟶ y) :
    (P.g f.right.left : P.S ⟶ P.S) ≫ P.ψ y = P.ψ x ≫ j.map f.right.right := by
  have hw : (γ f.right.left : D ⟶ D) ≫ y.right.hom = x.right.hom ≫ j.map f.right.right := f.right.w
  have hw' : x.hom ≫ f.right.right = y.hom := StructuredArrow.w f
  apply P.uniq
  · rw [← Category.assoc, P.hil, Category.assoc, (P.ψ_spec y).1, ← Category.assoc, (P.ψ_spec x).1, hw]
  · rw [← Category.assoc, P.hir, (P.ψ_spec y).2, ← Category.assoc, (P.ψ_spec x).2, ← j.map_comp, hw']

noncomputable def μ (F : C ⥤ ModuleCat.{w} R) : Mor (SingleObj.functor P.g ⋙ F)
    (StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ (Comma.snd (SingleObj.functor γ) j ⋙ j ⋙ F))
    (RingHom.id R) where
  G := StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ Comma.fst (SingleObj.functor γ) j
  τ x := (F.map (P.ψ x)).hom
  nat {x y} f a := by
    show (F.map (P.ψ y)).hom ((F.map (P.g f.right.left : P.S ⟶ P.S)).hom a) =
      (F.map (j.map f.right.right)).hom ((F.map (P.ψ x)).hom a)
    rw [← ModuleCat.comp_apply, ← F.map_comp, ← ModuleCat.comp_apply, ← F.map_comp, P.ψ_nat]

noncomputable def Ψ [j.Full] [j.Faithful] :
    Comma (SingleObj.functor P.g) j ⥤ StructuredArrow t (Comma.snd (SingleObj.functor γ) j) where
  obj X := StructuredArrow.mk (Y := ({ left := X.left, right := X.right, hom := P.il ≫ X.hom } :
      Comma (SingleObj.functor γ) j)) (j.preimage (P.ir ≫ X.hom))
  map {X Y} f := StructuredArrow.homMk
    { left := f.left, right := f.right
      w := by
        have hw : (P.g f.left : P.S ⟶ P.S) ≫ Y.hom = X.hom ≫ j.map f.right := f.w
        show (γ f.left : D ⟶ D) ≫ P.il ≫ Y.hom = (P.il ≫ X.hom) ≫ j.map f.right
        rw [← Category.assoc, ← P.hil, Category.assoc, hw, Category.assoc] }
    (by
      have hw : (P.g f.left : P.S ⟶ P.S) ≫ Y.hom = X.hom ≫ j.map f.right := f.w
      apply j.map_injective
      show j.map (j.preimage (P.ir ≫ X.hom) ≫ f.right) = j.map (j.preimage (P.ir ≫ Y.hom))
      rw [j.map_comp, Functor.map_preimage, Functor.map_preimage, Category.assoc, ← hw, ← Category.assoc, P.hir])
  map_id X := StructuredArrow.hom_ext _ _ (CommaMorphism.ext rfl rfl)
  map_comp f g := StructuredArrow.hom_ext _ _ (CommaMorphism.ext rfl rfl)

theorem ψΨ [j.Full] [j.Faithful] (T : Comma (SingleObj.functor P.g) j) : P.ψ (P.Ψ.obj T) = T.hom := by
  apply P.uniq
  · rw [(P.ψ_spec _).1]; rfl
  · rw [(P.ψ_spec _).2]; exact j.map_preimage _

theorem Ψ_full [j.Full] [j.Faithful] : P.Ψ.Full where
  map_surjective {X Y} f := by
    have w1 : (γ f.right.left : D ⟶ D) ≫ (P.il ≫ Y.hom) = (P.il ≫ X.hom) ≫ j.map f.right.right := f.right.w
    have w2 : j.preimage (P.ir ≫ X.hom) ≫ f.right.right = j.preimage (P.ir ≫ Y.hom) := StructuredArrow.w f
    have w : (P.g f.right.left : P.S ⟶ P.S) ≫ Y.hom = X.hom ≫ j.map f.right.right := by
      apply P.uniq
      · rw [← Category.assoc, P.hil, Category.assoc, w1, Category.assoc]
      · rw [← Category.assoc, P.hir, ← Category.assoc, ← j.map_preimage (P.ir ≫ X.hom), ← j.map_comp, w2,
          j.map_preimage]
    exact ⟨{ left := f.right.left, right := f.right.right, w := w }, StructuredArrow.hom_ext _ _ (CommaMorphism.ext rfl rfl)⟩

theorem Ψ_faithful [j.Full] [j.Faithful] : P.Ψ.Faithful where
  map_injective {_ _} {_ _} h := CommaMorphism.ext (congrArg (fun f => f.right.left) h) (congrArg (fun f => f.right.right) h)

theorem Ψ_essSurj [j.Full] [j.Faithful] : P.Ψ.EssSurj where
  mem_essImage Y := by
    let X : Comma (SingleObj.functor P.g) j := { left := Y.right.left, right := Y.right.right, hom := P.ψ Y }
    refine ⟨X, ⟨StructuredArrow.isoMk (Comma.isoMk (Iso.refl _) (Iso.refl _) ?_) ?_⟩⟩
    · show (SingleObj.functor γ).map (𝟙 Y.right.left) ≫ Y.right.hom = (P.il ≫ P.ψ Y) ≫ j.map (𝟙 _)
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      exact (P.ψ_spec Y).1.symm
    · show j.preimage (P.ir ≫ P.ψ Y) ≫ 𝟙 _ = Y.hom
      rw [Category.comp_id, (P.ψ_spec Y).2, j.preimage_map]

theorem Ψ_equiv [j.Full] [j.Faithful] : P.Ψ.IsEquivalence := by
  have := P.Ψ_full
  have := P.Ψ_faithful
  have := P.Ψ_essSurj
  exact {}

theorem μ_iso [j.Full] [j.Faithful] (F : C ⥤ ModuleCat.{w} R) (s : R) (hD : Desc s F j) (n : ℕ) :
    IsoLe (1 * s ^ (2 * (n + 1) + 3)) (n + 1) (P.μ F) := by
  intro q hq
  have h1 : UpTo (s ^ (2 * (n + 1) + 3)) ((gamCm F j (SingleObj.functor P.g)).pull q) :=
    CrystallineSemistableComparison.B.P.comma1 F j (SingleObj.functor P.g) s (fun φ a => gam_h F j _ φ a) hD (n + 1) q hq
  have := P.Ψ_equiv
  let F' := StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ (Comma.snd (SingleObj.functor γ) j ⋙ j ⋙ F)
  have hb : UpTo (1 : R) ((Mor.restrict F' P.Ψ).pull q) :=
    ((CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict F' P.Ψ).pull q) LinearMap.id (1 : R) 1).2.2.2.2).2
      (CrystallineSemistableComparison.P.adj F' P.Ψ _ P.Ψ.asEquivalence.toAdjunction q)
  let η : Comma.fst (SingleObj.functor P.g) j ⟶
      P.Ψ ⋙ (StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ Comma.fst (SingleObj.functor γ) j) :=
    { app := fun X => 𝟙 X.left
      naturality := fun X Y f => by
        show f.left ≫ 𝟙 Y.left = 𝟙 X.left ≫ f.left
        rw [Category.comp_id, Category.id_comp] }
  have heq : (Mor.restrict F' P.Ψ).pull q ∘ₗ (P.μ F).pull q = (gamCm F j (SingleObj.functor P.g)).pull q := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, ← (CrystallineSemistableComparison.P.pull_comp (P.μ F) (Mor.restrict F' P.Ψ) q x).1]
    refine (CrystallineSemistableComparison.P.prism (gamCm F j (SingleObj.functor P.g)) ((P.μ F).comp (Mor.restrict F' P.Ψ)) η ?_ q x).symm
    intro T a
    show (F.map (P.ψ (P.Ψ.obj T))).hom ((F.map ((SingleObj.functor P.g).map (𝟙 T.left))).hom a) = (F.map T.hom).hom a
    rw [CategoryTheory.Functor.map_id, F.map_id, ModuleCat.id_apply, P.ψΨ]
    rfl
  rw [← heq] at h1
  exact (CrystallineSemistableComparison.P.upTo_alg ((P.μ F).pull q) ((Mor.restrict F' P.Ψ).pull q) (1 : R) _).2.2.1 hb h1

end GamDat

end gam

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.gam : ∀ n : ℕ, ∃ N : ℕ, ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) [j.Full] [j.Faithful] (Γ : Type) [CommMonoid Γ] (D : C) (γ : Γ →* End D) (s : R), Desc s F j → (∀ t : C', ∃ (S : C) (il : D ⟶ S) (ir : j.obj t ⟶ S) (g : Γ →* End S), (∀ a, il ≫ (g a : S ⟶ S) = (γ a : D ⟶ D) ≫ il) ∧ (∀ a, ir ≫ (g a : S ⟶ S) = ir) ∧ (∀ (t' : C') (c : D ⟶ j.obj t') (φ : j.obj t ⟶ j.obj t'), ∃! ψ : S ⟶ j.obj t', il ≫ ψ = c ∧ ir ≫ ψ = φ) ∧ InjUpTo s (aug (SingleObj.functor g ⋙ F) fun _ => (F.map ir).hom) ∧ ExactUpTo s (aug (SingleObj.functor g ⋙ F) fun _ => (F.map ir).hom) (d (SingleObj.functor g ⋙ F) 0) ∧ ∀ i ≤ n, ExactUpTo s (d (SingleObj.functor g ⋙ F) i) (d (SingleObj.functor g ⋙ F) (i + 1))) → RI (s ^ N) n F (SingleObj.functor γ) := by
  intro n
  refine ⟨(2 * n + 3) + ((2 * n + 3) + (2 * n + 6) * (2 * n + 3)), ?_⟩
  intro R _ C _ C' _ F j _ _ Γ _ D γ s hD hT q hq
  have hA : UpTo (s ^ (2 * n + 3)) ((gamCm F j (SingleObj.functor γ)).pull q) :=
    CrystallineSemistableComparison.B.P.comma1 F j (SingleObj.functor γ) s (fun φ a => gam_h F j _ φ a) hD n q hq
  have hC : UpTo (s ^ (2 * n + 3)) ((Mor.restrict F j).pull q) :=
    CrystallineSemistableComparison.B.P.fib (Mor.restrict F j) s (fun T => hD T) n q hq
  have hS : UpTo ((s * (1 * s ^ (2 * (n + 1) + 3))) ^ (2 * n + 3))
      ((Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)).pull q) := by
    refine CrystallineSemistableComparison.B.P.fible (Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)) (s * (1 * s ^ (2 * (n + 1) + 3))) n
      (fun t => ?_) q hq
    obtain ⟨S, il, ir, g, hil, hir, hu, hinj, hex0, hex⟩ := hT t
    let P : GamDat γ j t := ⟨S, il, ir, g, hil, hir, hu⟩
    refine ⟨SingleObj Γ, inferInstance, SingleObj.functor g ⋙ F, P.μ F, fun _ => (F.map ir).hom, s,
      1 * s ^ (2 * (n + 1) + 3), rfl, ?_, ?_, P.μ_iso F s hD n, hinj, hex0, hex⟩
    · intro x a
      show (F.map (P.ψ x)).hom ((F.map ir).hom a) = (F.map (j.map x.hom)).hom a
      rw [← ModuleCat.comp_apply, ← F.map_comp, (P.ψ_spec x).2]
      rfl
    · intro x y φ a
      show (F.map (g φ : S ⟶ S)).hom ((F.map ir).hom a) = (F.map ir).hom a
      rw [← ModuleCat.comp_apply, ← F.map_comp, hir]
  have heq : (gamCm F j (SingleObj.functor γ)).pull q ∘ₗ (Mor.restrict F (SingleObj.functor γ)).pull q =
      (Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)).pull q ∘ₗ (Mor.restrict F j).pull q := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      ← (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F (SingleObj.functor γ)) (gamCm F j (SingleObj.functor γ)) q x).1,
      ← (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F j) (Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)) q x).1]
    refine CrystallineSemistableComparison.P.prism _ _ (Comma.natTrans (SingleObj.functor γ) j) (fun T a => rfl) q x
  have h2 := (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).1 hC hS
  rw [← heq] at h2
  have h3 := (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).2.2.1 hA h2
  have e : s ^ ((2 * n + 3) + ((2 * n + 3) + (2 * n + 6) * (2 * n + 3))) =
      s ^ (2 * n + 3) * (s ^ (2 * n + 3) * (s * (1 * s ^ (2 * (n + 1) + 3))) ^ (2 * n + 3)) := by ring
  rw [e]
  exact h3
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.bnat : ∀ {R : Type} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M] (N : SingleObj (Multiplicative ℕ) ⥤ ModuleCat.{w} R) (a : M →ₗ[R] N.obj (SingleObj.star _)) (s : R), (∀ x, (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (Multiplicative.ofAdd 1)).hom (a x) = a x) → Acyc1 s a (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (Multiplicative.ofAdd 1)).hom → (cx N).ResUpTo s (aug N fun _ => a) := fun N a s h H =>
  GlobalTheory.CompanionTheory.NatCoh.resUpTo_of_acyc N a s h H.1 (fun y hy => H.2.1 y (sub_eq_zero.1 hy)) H.2.2
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

theorem kstep_aug_d {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {M : Type w'} [AddCommGroup M] [Module R M] (e : ∀ T : C, M →ₗ[R] F.obj T)
    (he : ∀ {T T' : C} (φ : T ⟶ T') x, (F.map φ).hom (e T x) = e T' x) (x : M) :
    d F 0 (aug F e x) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (GlobalTheory.CatH.toLast i s)).hom (e _ x) = 0
  simp only [he, Fin.sum_univ_two]
  simp

def kstepLast (d k : ℕ) : Gam (d + 1) := Multiplicative.ofAdd (Pi.single (Fin.last d) k)

section kstep

variable {d : ℕ} (π : Gam (d + 1) →* Gam d)
  (hπ : ∀ a k, Multiplicative.toAdd (π a) k = Multiplicative.toAdd a k.castSucc)

include hπ in
theorem kstep_π_last (k : ℕ) : π (kstepLast d k) = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [hπ]
  simp [kstepLast, Fin.castSucc_ne_last]

def kstepL (hπ : ∀ a k, Multiplicative.toAdd (π a) k = Multiplicative.toAdd a k.castSucc) : SingleObj (Multiplicative ℕ) ⥤ StructuredArrow (SingleObj.star (Gam d)) π.toFunctor where
  obj _ := StructuredArrow.mk (Y := SingleObj.star (Gam (d + 1)))
    (show SingleObj.star (Gam d) ⟶ π.toFunctor.obj (SingleObj.star _) from (1 : Gam d))
  map k := StructuredArrow.homMk (show SingleObj.star (Gam (d + 1)) ⟶ SingleObj.star _ from
      kstepLast d (Multiplicative.toAdd k)) (by
    simp only [StructuredArrow.mk_hom_eq_self]
    exact kstep_π_last π hπ _)
  map_id _ := by
    apply StructuredArrow.hom_ext
    change kstepLast d (Multiplicative.toAdd (1 : Multiplicative ℕ)) = (1 : Gam (d + 1))
    simp [kstepLast]
  map_comp f g := by
    apply StructuredArrow.hom_ext
    change kstepLast d (Multiplicative.toAdd ((show Multiplicative ℕ from g) * (show Multiplicative ℕ from f))) = kstepLast d (Multiplicative.toAdd (g : Multiplicative ℕ)) * kstepLast d (Multiplicative.toAdd (f : Multiplicative ℕ))
    simp [kstepLast, Pi.single_add]

def kstepU : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor ⥤ SingleObj (Multiplicative ℕ) where
  obj _ := SingleObj.star _
  map f := Multiplicative.ofAdd (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d))
  map_id _ := by
    change Multiplicative.ofAdd (Multiplicative.toAdd (1 : Gam (d + 1)) (Fin.last d)) = 1
    simp
  map_comp f g := by
    change Multiplicative.ofAdd (Multiplicative.toAdd ((show Gam (d + 1) from g.right) * (show Gam (d + 1) from f.right)) (Fin.last d)) =
      Multiplicative.ofAdd (Multiplicative.toAdd (g.right : Gam (d + 1)) (Fin.last d)) *
        Multiplicative.ofAdd (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d))
    simp only [toAdd_mul, Pi.add_apply, ofAdd_add]
    rfl

def kstepSnoc (b : Gam d) (k : ℕ) : Gam (d + 1) :=
  Multiplicative.ofAdd (Fin.snoc (α := fun _ => ℕ) (Multiplicative.toAdd b) k)

include hπ in
theorem kstep_π_snoc (b : Gam d) (k : ℕ) : π (kstepSnoc b k) = b := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [hπ]
  simp [kstepSnoc]

include hπ in
theorem kstep_snoc_eq (a : Gam (d + 1)) : kstepSnoc (π a) (Multiplicative.toAdd a (Fin.last d)) = a := by
  apply Multiplicative.toAdd.injective
  funext i
  induction i using Fin.lastCases with
  | last => simp [kstepSnoc]
  | cast i => simp [kstepSnoc, hπ]

def kstepAdj : kstepL π hπ ⊣ kstepU π :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => show X ⟶ (kstepU π).obj Y from
            Multiplicative.ofAdd (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d))
          invFun := fun k => StructuredArrow.homMk
            (show ((kstepL π hπ).obj X).right ⟶ Y.right from
              kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (show Multiplicative ℕ from k)))
            (kstep_π_snoc π hπ _ _)
          left_inv := fun f => by
            apply StructuredArrow.hom_ext
            change kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (f.right : Gam (d + 1)) (Fin.last d)) = f.right
            have w : (show Gam d from Y.hom) = π f.right := (StructuredArrow.w f).symm
            rw [w]
            exact kstep_snoc_eq π hπ _
          right_inv := fun k => by
            change Multiplicative.ofAdd (Multiplicative.toAdd
              (kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (show Multiplicative ℕ from k))) (Fin.last d)) = k
            simp [kstepSnoc] }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        apply StructuredArrow.hom_ext
        change kstepSnoc (show Gam d from Y.hom)
            (Multiplicative.toAdd ((show Multiplicative ℕ from g) * (show Multiplicative ℕ from f))) =
          kstepSnoc (show Gam d from Y.hom) (Multiplicative.toAdd (show Multiplicative ℕ from g)) *
            kstepLast d (Multiplicative.toAdd (show Multiplicative ℕ from f))
        apply Multiplicative.toAdd.injective
        funext i
        induction i using Fin.lastCases with
        | last => simp [kstepSnoc, kstepLast]
        | cast i => simp [kstepSnoc, kstepLast, Fin.castSucc_ne_last]
      homEquiv_naturality_right := fun f g => (kstepU π).map_comp f g }

end kstep

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.kstep : ∀ {R : Type} [CommRing R] {d : ℕ} (M : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (N : SingleObj (Gam (d + 1)) ⥤ ModuleCat.{w} R) (π : Gam (d + 1) →* Gam d) (hπ : ∀ a k, Multiplicative.toAdd (π a) k = Multiplicative.toAdd a k.castSucc) (τ : M.obj (SingleObj.star _) →ₗ[R] N.obj (SingleObj.star _)) (h : ∀ (a : Gam (d + 1)) x, τ ((M.map (X := SingleObj.star _) (Y := SingleObj.star _) (π a)).hom x) = (N.map (X := SingleObj.star _) (Y := SingleObj.star _) a).hom (τ x)) (s : R), Acyc1 s τ (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen (Fin.last d))).hom → ∀ n, IsoLe (s ^ (2 * n + 3)) n (⟨π.toFunctor, fun _ => τ, fun φ x => h φ x⟩ : Mor M N (RingHom.id R)) := by
  intro R _ d M N π hπ τ h s hA n
  apply CrystallineSemistableComparison.B.P.fib
  intro T
  have hM1 : M.map (X := SingleObj.star _) (Y := SingleObj.star _) (1 : Gam d) = 𝟙 _ := M.map_id _
  obtain rfl : T = SingleObj.star (Gam d) := Subsingleton.elim _ _
  let F' : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor ⥤ ModuleCat.{w} R :=
    StructuredArrow.proj (SingleObj.star (Gam d)) π.toFunctor ⋙ N
  let e : ∀ x : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor,
      M.obj (SingleObj.star (Gam d)) →ₗ[R] F'.obj x := fun x => τ ∘ₗ (M.map x.hom).hom
  have he : ∀ {x y : StructuredArrow (SingleObj.star (Gam d)) π.toFunctor} (φ : x ⟶ y) a,
      (F'.map φ).hom (e x a) = e y a := by
    intro x y φ a
    have h1 := h φ.right ((M.map x.hom).hom a)
    refine h1.symm.trans ?_
    change τ ((M.map x.hom ≫ M.map (π.toFunctor.map φ.right)).hom a) = τ ((M.map y.hom).hom a)
    rw [← M.map_comp, StructuredArrow.w φ]
  have hfix : ∀ x, (N.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen (Fin.last d))).hom (τ x) = τ x := by
    intro x
    rw [← h, show π (gen (Fin.last d)) = 1 from kstep_π_last π hπ 1, hM1]
    rfl
  have hb := CrystallineSemistableComparison.B.P.bnat (kstepL π hπ ⋙ F') τ s hfix hA
  have hadj := CrystallineSemistableComparison.P.adj F' (kstepL π hπ) (kstepU π) (kstepAdj π hπ)
  have hup : ∀ k, UpTo (1 : R) ((Mor.restrict F' (kstepL π hπ)).hom.mapH k) := fun k =>
    ((CrystallineSemistableComparison.P.upTo_alg _ (LinearMap.id (R := R)) (1 : R) 1).2.2.2.2).2 (hadj k)
  have hε : (Mor.restrict F' (kstepL π hπ)).hom.f 0 ∘ₗ aug F' e = aug (kstepL π hπ ⋙ F') fun _ => τ := by
    refine LinearMap.ext fun x => funext fun s => ?_
    change τ ((M.map (1 : Gam d)).hom x) = τ x
    rw [hM1]
    rfl
  have htr := (CrystallineSemistableComparison.P.res_transfer (Mor.restrict F' (kstepL π hπ)).hom (aug F' e) s 1 hup).2
    (kstep_aug_d F' e he) (hε ▸ hb)
  rw [mul_one] at htr
  exact htr
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

def torsRLe {R : Type} [CommRing R] {M : Type w'} [AddCommGroup M] [Module R M] (K : Cx.{w} R) (s : R) (n : ℕ)
    (ε : M →ₗ[R] K.X 0) : Prop :=
  (∀ x, K.d 0 (ε x) = 0) ∧ InjUpTo s ε ∧ ExactUpTo s ε (K.d 0) ∧ ∀ i ≤ n, ExactUpTo s (K.d i) (K.d (i + 1))

theorem torsRLe.mul {R : Type} [CommRing R] {M : Type w'} [AddCommGroup M] [Module R M] {K : Cx.{w} R} {s : R} {n : ℕ}
    {ε : M →ₗ[R] K.X 0} (h : torsRLe K s n ε) (t : R) : torsRLe K (s * t) n ε := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨h0, fun x hx => ?_, fun y hy => ?_, fun i hi y hy => ?_⟩
  · rw [mul_comm, mul_smul, h1 x hx, smul_zero]
  · obtain ⟨x, hx⟩ := h2 y hy
    exact ⟨t • x, by rw [map_smul, hx, smul_smul, mul_comm]⟩
  · obtain ⟨x, hx⟩ := h3 i hi y hy
    exact ⟨t • x, by rw [map_smul, hx, smul_smul, mul_comm]⟩

theorem tors_resUpTo_mul {R : Type} [CommRing R] {M : Type w'} [AddCommGroup M] [Module R M] {K : Cx.{w} R} {s : R}
    {ε : M →ₗ[R] K.X 0} (h : K.ResUpTo s ε) (t : R) : K.ResUpTo (s * t) ε := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨h0, fun x hx => ?_, fun y hy => ?_, fun i y hy => ?_⟩
  · rw [mul_comm, mul_smul, h1 x hx, smul_zero]
  · obtain ⟨x, hx⟩ := h2 y hy
    exact ⟨t • x, by rw [map_smul, hx, smul_smul, mul_comm]⟩
  · obtain ⟨x, hx⟩ := h3 i y hy
    exact ⟨t • x, by rw [map_smul, hx, smul_smul, mul_comm]⟩

theorem torsRLe.transfer {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    {M : Type v''} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} {s s' : R} {n : ℕ}
    (h0 : InjUpTo s' (φ.mapH 0)) (hS : ∀ k ≤ n + 1, SurjUpTo s' (φ.mapH k)) (h : torsRLe K s n ε) :
    torsRLe L (s * s') n (φ.f 0 ∘ₗ ε) := by
  obtain ⟨c0, c1, c2, c3⟩ := h
  have cz : ∀ x, L.d 0 (φ.f 0 (ε x)) = 0 := fun x => by rw [φ.comm, c0, map_zero]
  refine ⟨cz, fun x hx => ?_, fun y hy => ?_, fun i hi y hy => ?_⟩
  · have hx' : φ.f 0 (ε x) = 0 := hx
    have e1 : φ.mapH 0 (K.cls (ε x) (c0 x)) = 0 := by
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 (ε x) (c0 x) (cz x), (CrystallineSemistableComparison.P.cls_surj L 0).2.1, hx']
      exact Submodule.zero_mem _
    have e2 := h0 _ e1
    have hs : K.d 0 (s' • ε x) = 0 := by rw [map_smul, c0, smul_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj K 0).2.2.2.2 s' (ε x) (c0 x) hs, (CrystallineSemistableComparison.P.cls_surj K 0).2.1] at e2
    have e3 : s' • ε x = 0 := (Submodule.mem_bot R).1 e2
    rw [← map_smul] at e3
    rw [mul_smul, c1 _ e3]
  · obtain ⟨z, hz⟩ := hS 0 (Nat.zero_le _) (L.cls y hy)
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 z
    have hb : L.d 0 (φ.f 0 a) = 0 := by rw [φ.comm, ha, map_zero]
    have hsy : L.d 0 (s' • y) = 0 := by rw [map_smul, hy, smul_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls φ 0 a ha hb, ← (CrystallineSemistableComparison.P.cls_surj L 0).2.2.2.2 s' y hy hsy,
      (CrystallineSemistableComparison.P.cls_surj L 0).2.2.1] at hz
    have e3 : φ.f 0 a = s' • y := sub_eq_zero.1 ((Submodule.mem_bot R).1 hz)
    obtain ⟨x, hx⟩ := c2 a ha
    refine ⟨x, ?_⟩
    change φ.f 0 (ε x) = _
    rw [hx, map_smul, e3, smul_smul]
  · obtain ⟨z, hz⟩ := hS (i + 1) (by omega) (L.cls y hy)
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K (i + 1)).1 z
    have hb : L.d (i + 1) (φ.f (i + 1) a) = 0 := by rw [φ.comm, ha, map_zero]
    have hsy : L.d (i + 1) (s' • y) = 0 := by rw [map_smul, hy, smul_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls φ (i + 1) a ha hb, ← (CrystallineSemistableComparison.P.cls_surj L (i + 1)).2.2.2.2 s' y hy hsy,
      (CrystallineSemistableComparison.P.cls_surj L (i + 1)).2.2.1] at hz
    obtain ⟨b, hb'⟩ := hz
    obtain ⟨c, hc⟩ := c3 i hi a ha
    refine ⟨φ.f i c - s • b, ?_⟩
    rw [map_sub, map_smul, φ.comm, hc, map_smul, hb', smul_sub, sub_sub_cancel, smul_smul]

end CrystallineSemistableComparison.B

namespace CrystallineSemistableComparison.B

def torsPi (e : ℕ) : Gam (e + 1) →* Gam e where
  toFun a := Multiplicative.ofAdd fun k => Multiplicative.toAdd a k.castSucc
  map_one' := rfl
  map_mul' _ _ := rfl

def torsLast (e : ℕ) : Gam (e + 1) →* Multiplicative ℕ where
  toFun a := Multiplicative.ofAdd (Multiplicative.toAdd a (Fin.last e))
  map_one' := rfl
  map_mul' _ _ := rfl

section Tower

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {j : C' ⥤ C} {U : UF C}

abbrev torsGp (L : Line j U) (S : C) (m : ℕ) : End (L.Ξ.obj S) := End.of (L.γ.app S) ^ m

def torsStep (L : Line j U) {e : ℕ} {S : C} (g : Gam e →* End S) : Gam (e + 1) →* End (L.Ξ.obj S) :=
  (MonoidHom.noncommCoprod ((L.Ξ.mapEnd S).comp (g.comp (torsPi e))) ((powersHom (End (L.Ξ.obj S)) (End.of (L.γ.app S))).comp (torsLast e))
    (fun a b => by
      refine Commute.pow_right ?_ _
      show L.γ.app S ≫ L.Ξ.map (g (torsPi e a)) = L.Ξ.map (g (torsPi e a)) ≫ L.γ.app S
      exact (L.γ.naturality _).symm)).comp ((MonoidHom.id _).prod (MonoidHom.id _))

theorem torsStep_apply (L : Line j U) {e : ℕ} {S : C} (g : Gam e →* End S) (a : Gam (e + 1)) :
    (torsStep L g a : L.Ξ.obj S ⟶ L.Ξ.obj S) =
      (torsGp L S (Multiplicative.toAdd a (Fin.last e)) : L.Ξ.obj S ⟶ L.Ξ.obj S) ≫ L.Ξ.map (g (torsPi e a)) :=
  rfl

theorem tors_i_pow (L : Line j U) (S : C) (m : ℕ) :
    L.i.app S ≫ (torsGp L S m : L.Ξ.obj S ⟶ L.Ξ.obj S) = L.i.app S := by
  have h1 : L.i.app S ≫ L.γ.app S = L.i.app S := by
    have := congrArg (fun t => NatTrans.app t S) L.iγ
    simpa using this
  induction m with
  | zero => exact Category.comp_id _
  | succ m ih =>
    rw [torsGp, pow_succ, End.mul_def, ← Category.assoc, h1, ← torsGp, ih]

theorem tors_pow_η (L : Line j U) (S : C) (m : ℕ) :
    U.map (torsGp L S m : L.Ξ.obj S ⟶ L.Ξ.obj S) (L.η S) = U.q _ ^ m * L.η S := by
  induction m with
  | zero => rw [pow_zero, one_mul]; exact U.map_id _ _
  | succ m ih =>
    rw [torsGp, pow_succ, End.mul_def, U.map_comp, L.γη, map_mul, ← torsGp, ih, U.map_q, pow_succ', mul_assoc]

theorem tors_istep (L : Line j U) {e : ℕ} {S : C} (g : Gam e →* End S) (a : Gam (e + 1)) :
    L.i.app S ≫ (torsStep L g a : L.Ξ.obj S ⟶ L.Ξ.obj S) = (g (torsPi e a) : S ⟶ S) ≫ L.i.app S := by
  rw [torsStep_apply, ← Category.assoc, tors_i_pow]
  exact (L.i.naturality _).symm

theorem torsStep_gen (L : Line j U) {e : ℕ} {S : C} (g : Gam e →* End S) :
    (torsStep L g (gen (Fin.last e)) : L.Ξ.obj S ⟶ L.Ξ.obj S) = L.γ.app S := by
  have hp : torsPi e (gen (Fin.last e)) = 1 := by
    funext k
    exact Pi.single_eq_of_ne (Fin.castSucc_ne_last k) _
  rw [torsStep_apply, hp, map_one]
  show _ ≫ L.Ξ.map (𝟙 S) = _
  rw [L.Ξ.map_id, Category.comp_id]
  rw [show Multiplicative.toAdd (gen (Fin.last e)) (Fin.last e) = 1 from Pi.single_eq_same _ _, torsGp, pow_one]

end Tower

end CrystallineSemistableComparison.B

namespace CrystallineSemistableComparison.B

theorem tors_tower {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (U : UF C) (L : Line j U) (s : R) (n : ℕ)
    (hA : ∀ T, Acyc1 s (F.map (L.i.app T)).hom (F.map (L.γ.app T)).hom) (T : C) :
    ∀ e : ℕ, ∃ (S : C) (ir : T ⟶ S) (η : Fin e → U.U S) (g : Gam e →* End S),
      (∀ a, ir ≫ (g a : S ⟶ S) = ir) ∧
      (∀ a k, U.map (g a : S ⟶ S) (η k) = U.q S ^ (Multiplicative.toAdd a k) * η k) ∧
      (∀ (t' : C') (φ : T ⟶ j.obj t') (b : Fin e → U.U (j.obj t')),
        ∃! ψ : S ⟶ j.obj t', ir ≫ ψ = φ ∧ ∀ k, U.map ψ (η k) = b k) ∧
      torsRLe (cx (SingleObj.functor g ⋙ F)) (s ^ (e * (2 * n + 5))) n
        (aug (SingleObj.functor g ⋙ F) fun _ => (F.map ir).hom) := by
  intro e
  induction e with
  | zero =>
    have : ∀ Y : SingleObj (Gam 0), Unique (SingleObj.star (Gam 0) ⟶ Y) := fun Y =>
      ⟨⟨(1 : Gam 0)⟩, fun a => show (a : Fin 0 → ℕ) = (1 : Gam 0) from funext fun k => k.elim0⟩
    have hI : Limits.IsInitial (SingleObj.star (Gam 0)) := Limits.IsInitial.ofUnique _
    refine ⟨T, 𝟙 T, fun k => k.elim0, 1, fun a => Category.comp_id _, fun a k => k.elim0,
      fun t' φ b => ⟨φ, ⟨Category.id_comp _, fun k => k.elim0⟩, fun ψ h => by rw [← h.1, Category.id_comp]⟩, ?_⟩
    have h := CrystallineSemistableComparison.P.initial (SingleObj.functor (1 : Gam 0 →* End T) ⋙ F) _ hI
    rw [zero_mul, pow_zero]
    exact ⟨h.1, h.2.1, h.2.2.1, fun i _ => h.2.2.2 i⟩
  | succ e ih =>
    obtain ⟨S, ir, η, g, h1, h2, h3, h4⟩ := ih
    refine ⟨L.Ξ.obj S, ir ≫ L.i.app S, Fin.lastCases (L.η S) (fun k => U.map (L.i.app S) (η k)), torsStep L g,
      fun a => ?_, fun a k => ?_, fun t' φ b => ?_, ?_⟩
    · rw [Category.assoc, tors_istep, ← Category.assoc, h1]
    · refine Fin.lastCases ?_ (fun k => ?_) k
      · simp only [Fin.lastCases_last]
        rw [torsStep_apply, U.map_comp, tors_pow_η, map_mul, map_pow, U.map_q, L.map_η]
      · simp only [Fin.lastCases_castSucc]
        rw [← U.map_comp, tors_istep, U.map_comp]
        erw [h2 (torsPi e a) k]
        rw [map_mul, map_pow, U.map_q]
        rfl
    · obtain ⟨χ, ⟨hχ1, hχ2⟩, hχu⟩ := h3 t' φ (fun k => b k.castSucc)
      obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := L.univ S t' χ (b (Fin.last e))
      refine ⟨ψ, ⟨by rw [Category.assoc, hψ1, hχ1], fun k => ?_⟩, fun ψ' h' => ?_⟩
      · refine Fin.lastCases ?_ (fun k => ?_) k
        · simp only [Fin.lastCases_last]; exact hψ2
        · simp only [Fin.lastCases_castSucc]; rw [← U.map_comp, hψ1]; exact hχ2 k
      · refine hψu ψ' ⟨hχu _ ⟨by rw [← Category.assoc]; exact h'.1, fun k => ?_⟩, ?_⟩
        · have := h'.2 k.castSucc
          simp only [Fin.lastCases_castSucc] at this
          rw [← U.map_comp] at this
          exact this
        · have := h'.2 (Fin.last e)
          simp only [Fin.lastCases_last] at this
          exact this
    · have hk := CrystallineSemistableComparison.B.P.kstep (SingleObj.functor g ⋙ F) (SingleObj.functor (torsStep L g) ⋙ F) (torsPi e)
        (fun a k => rfl) (F.map (L.i.app S)).hom (fun a x => by
          have h := congrArg (fun f => (F.map f).hom x) (tors_istep L g a)
          simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
          exact h.symm) s
        (by
          change Acyc1 s (F.map (L.i.app S)).hom (F.map (torsStep L g (gen (Fin.last e)))).hom
          rw [torsStep_gen]
          exact hA S) (n + 1)
      have ht := torsRLe.transfer _ (hk 0 (Nat.zero_le _)).1 (fun k hk' => (hk k hk').2) h4
      rw [← pow_add] at ht
      rw [show (e + 1) * (2 * n + 5) = e * (2 * n + 5) + (2 * (n + 1) + 3) by ring]
      convert ht using 1
      refine LinearMap.ext fun x => funext fun c => ?_
      change (F.map (ir ≫ L.i.app S)).hom x = (F.map (L.i.app S)).hom ((F.map ir).hom x)
      rw [F.map_comp]
      rfl

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.tors : ∀ d n : ℕ, ∃ N : ℕ, ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) [j.Full] [j.Faithful] (U : UF C) (D : C) (A : Act j U d D) (L : Line j U) (s : R), Desc s F j → (∀ T, Acyc1 s (F.map (L.i.app T)).hom (F.map (L.γ.app T)).hom) → RI (s ^ N) n F A.ι := by
  intro d n
  obtain ⟨N₀, hN₀⟩ := CrystallineSemistableComparison.B.P.gam.{w, v, u, v', u'} n
  refine ⟨(d * (2 * n + 5) + 1) * N₀, ?_⟩
  intro R _ C _ C' _ F j _ _ U D A L s hD hA
  rw [pow_mul]
  unfold Act.ι
  refine hN₀ F j (Gam d) D A.γ (s ^ (d * (2 * n + 5) + 1)) (fun T => ?_) (fun t => ?_)
  · rw [pow_succ']
    exact tors_resUpTo_mul (hD T) _
  · obtain ⟨S, ir, η, g, h1, h2, h3, h4⟩ := tors_tower F j U L s n hA (j.obj t) d
    obtain ⟨c₀⟩ := A.ne t
    have h4' := h4.mul s
    rw [← pow_succ] at h4'
    refine ⟨S, A.act η (c₀ ≫ ir), ir, g, fun a => ?_, h1, fun t' c φ => ?_, h4'.2.1, h4'.2.2.1, h4'.2.2.2⟩
    · have e1 : A.act η (c₀ ≫ ir) ≫ (g a : S ⟶ S) =
          A.act (fun k => U.q S ^ (Multiplicative.toAdd a k)) (A.act η (c₀ ≫ ir)) := by
        rw [A.act_comp, Category.assoc, h1, ← A.act_mul]
        congr 1
        funext k
        exact h2 a k
      have e2 : (A.γ a : D ⟶ D) ≫ A.act η (c₀ ≫ ir) =
          A.act (fun k => U.q S ^ (Multiplicative.toAdd a k)) (A.act η (c₀ ≫ ir)) := by
        show A.act (fun k => U.q D ^ (Multiplicative.toAdd a k)) (𝟙 D) ≫ _ = _
        rw [A.act_comp, Category.id_comp]
        congr 1
        funext k
        rw [map_pow, U.map_q]
      rw [e1, e2]
    · obtain ⟨a, ha, hau⟩ := A.trans t' (c₀ ≫ φ) c
      obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := h3 t' φ a
      refine ⟨ψ, ⟨?_, hψ1⟩, fun ψ' h' => ?_⟩
      · rw [A.act_comp, Category.assoc, hψ1, show (fun k => U.map ψ (η k)) = a from funext hψ2]
        exact ha
      · refine hψu ψ' ⟨h'.2, fun k => ?_⟩
        have hh := h'.1
        rw [A.act_comp, Category.assoc, h'.2] at hh
        exact congrFun (hau _ hh) k
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section NiCoh

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem ni_nat {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') {T T' : C} (φ : T ⟶ T') (x : F.obj T) :
    (β.app T').hom ((F.map φ).hom x) = (F'.map φ).hom ((β.app T).hom x) := by
  rw [← ModuleCat.comp_apply, β.naturality, ModuleCat.comp_apply]

theorem ni_pull_cls {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (n : ℕ) (a : Cn F n) (ha : d F n a = 0) :
    ∃ hb, (Mor.ofNatTrans β).pull n ((cx F).cls a ha) = (cx F').cls (fun s => (β.app _).hom (a s)) hb := by
  have hb : d F' n (fun s => (β.app _).hom (a s)) = 0 :=
    ((Mor.ofNatTrans β).d_pullC n a).trans (by rw [ha, map_zero])
  exact ⟨hb, CrystallineSemistableComparison.P.mapH_cls (Mor.ofNatTrans β).hom n a ha hb⟩

theorem ni_pull_add {F F' : C ⥤ ModuleCat.{w} R} (β β' : F ⟶ F') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β + β')).pull n x = (Mor.ofNatTrans β).pull n x + (Mor.ofNatTrans β').pull n x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β + β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n a ha
  rw [e1, e2, e3, ← (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.2.2.1 _ _ h2 h3 (by rw [map_add, h2, h3, add_zero])]
  congr 1

theorem ni_pull_zero {F F' : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (0 : F ⟶ F')).pull n x = 0 := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (0 : F ⟶ F') n a ha
  rw [e1, (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.1]
  have : (fun s => ((0 : F ⟶ F').app _).hom (a s)) = (0 : Cn F' n) := by
    funext s
    simp only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply, Pi.zero_apply]
  rw [this]
  exact Submodule.zero_mem _

theorem ni_pull_sum {ι : Type} {F F' : C ⥤ ModuleCat.{w} R} (β : ι → (F ⟶ F')) (S : Finset ι) (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (∑ k ∈ S, β k)).pull n x = ∑ k ∈ S, (Mor.ofNatTrans (β k)).pull n x := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ni_pull_zero]
  | insert k S hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, ni_pull_add, ih]

theorem ni_pull_comp {F F' F'' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (β' : F' ⟶ F'') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β ≫ β')).pull n x = (Mor.ofNatTrans β').pull n ((Mor.ofNatTrans β).pull n x) := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β ≫ β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n _ h2
  rw [e1, e2, e3]
  rfl

theorem ni_pull_id {F : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (𝟙 F)).pull n x = x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (𝟙 F) n a ha
  rw [e1]
  rfl

def fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) : SubF F where
  S T := LinearMap.ker ((e.app T).hom - LinearMap.id)
  map_mem := fun {_ _} φ {_} hx => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    rw [ni_nat, hx]

theorem mem_fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (T : C) (x : F.obj T) :
    x ∈ (fixF e).S T ↔ (e.app T).hom x = x := by
  change x ∈ LinearMap.ker ((e.app T).hom - LinearMap.id) ↔ _
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

def fixP {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : F ⟶ (fixF e).fn where
  app T := ModuleCat.ofHom (LinearMap.codRestrict _ (e.app T).hom fun x => by
    rw [mem_fixF, ← ModuleCat.comp_apply, ← NatTrans.comp_app, he])
  naturality T T' φ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (ni_nat e φ x))

def fixI {F : C ⥤ ModuleCat.{w} R} (S : SubF F) : S.fn ⟶ F where
  app T := ModuleCat.ofHom (S.S T).subtype
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem fixP_fixI {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : fixP e he ≫ fixI (fixF e) = e :=
  NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

def gNat {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) : G ⟶ G where
  app _ := G.map (X := SingleObj.star _) (Y := SingleObj.star _) g
  naturality X Y a := by
    rw [← G.map_comp, ← G.map_comp]
    congr 1
    exact mul_comm (g : Gam d) (a : Gam d)

theorem gNat_pull {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (n : ℕ) (x : H G n) :
    (Mor.ofNatTrans (gNat G g)).pull n x = x := by
  have := CrystallineSemistableComparison.P.prism (Mor.ofNatTrans (gNat G g)) (Mor.id G)
    { app := fun _ => (g : SingleObj.star (Gam d) ⟶ SingleObj.star (Gam d)), naturality := fun _ _ a => mul_comm (g : Gam d) (a : Gam d) }
    (fun T x => rfl) n x
  rw [this]
  exact ((CrystallineSemistableComparison.P.pull_comp (Mor.id G) (Mor.id G) n x).2)

theorem killed_of {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (s : R)
    (hu : ∀ T, UpTo s ((gNat G g - 𝟙 G).app T).hom) (n : ℕ) (z : H G n) : s ^ 2 • z = 0 := by
  obtain ⟨x, hx⟩ := (CrystallineSemistableComparison.P.coef_upTo _ s hu n).2 z
  rw [← hx]
  have e1 := ni_pull_add (gNat G g - 𝟙 G) (𝟙 G) n x
  rw [sub_add_cancel, gNat_pull, ni_pull_id] at e1
  calc _ = ((Mor.ofNatTrans (gNat G g - 𝟙 G)).pull n x + x) - x := (add_sub_cancel_right _ _).symm
    _ = x - x := by rw [← e1]
    _ = 0 := sub_self x

theorem ni_killed {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N) (h : NI s α) (k : Fin d)
    (n : ℕ) (z : H (fixF (h.π k)).fn n) : s ^ 2 • z = 0 := by
  refine killed_of _ (gen k) s (fun T => ?_) n z
  change UpTo s ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom
  have hδ : ∀ y : (fixF (h.π k)).fn.obj (SingleObj.star _), ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom y =
      ((fixF (h.π k)).fn.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k)).hom y - y := fun y => rfl
  refine ⟨fun y hy => ?_, fun y => ?_⟩
  · rw [hδ, sub_eq_zero] at hy
    have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    exact Subtype.ext (h.inj k y.1 h1 (congrArg Subtype.val hy))
  · have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    obtain ⟨x, hx, hx2⟩ := h.surj k y.1 h1
    exact ⟨⟨x, (mem_fixF (h.π k) _ x).2 hx⟩, by rw [hδ]; exact Subtype.ext hx2⟩

end NiCoh

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.ni_coh : ∀ {R : Type} [CommRing R] {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N), NI s α → ∀ n, IsoLe (s ^ 2) n (Mor.ofNatTrans α) := by
  intro R _ d s M N α h n j _
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · have e := ni_pull_comp α h.ρ j x
    rw [h.αρ, ni_pull_id, hx, map_zero] at e
    rw [e, smul_zero]
  · refine ⟨(Mor.ofNatTrans h.ρ).pull j (s ^ 2 • y), ?_⟩
    rw [← ni_pull_comp]
    have e := ni_pull_add (h.ρ ≫ α) (∑ k, h.π k) j (s ^ 2 • y)
    rw [h.sum, ni_pull_id, ni_pull_sum] at e
    have hk : ∀ k, (Mor.ofNatTrans (h.π k)).pull j (s ^ 2 • y) = 0 := by
      intro k
      rw [← fixP_fixI (h.π k) (h.idem k), ni_pull_comp, map_smul, ni_killed s α h k, map_zero]
    rw [Finset.sum_eq_zero (fun k _ => hk k), add_zero] at e
    exact e.symm
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

lemma gl_res_one {R : Type} [CommRing R] {K : Cx.{w} R} {M : Type w'} [AddCommGroup M] [Module R M]
    (ε : M →ₗ[R] K.X 0) (s : R) (h : K.ResUpTo 1 ε) : K.ResUpTo s ε := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨h0, fun x hx => by rw [← one_smul R x, h1 x hx, smul_zero], fun y hy => ?_, fun m y hy => ?_⟩
  · obtain ⟨x, hx⟩ := h2 y hy
    exact ⟨s • x, by rw [map_smul, hx, one_smul]⟩
  · obtain ⟨x, hx⟩ := h3 m y hy
    exact ⟨s • x, by rw [map_smul, hx, one_smul]⟩

lemma gl_desc_id {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (s : R) :
    Desc s F (𝟭 C) := by
  intro T
  have hI : Limits.IsInitial (StructuredArrow.mk (𝟙 T) : StructuredArrow T (𝟭 C)) :=
    StructuredArrow.mkIdInitial (T := 𝟭 C) (Y := T)
  have h := CrystallineSemistableComparison.P.initial (StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F) _ hI
  have e : (aug (StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F) fun x =>
      ((StructuredArrow.proj T (𝟭 C) ⋙ 𝟭 C ⋙ F).map (hI.to x)).hom) = unAug F (𝟭 C) T := by
    unfold unAug
    congr 1
    funext x
    have hx : (hI.to x).right = x.hom := by simpa using StructuredArrow.w (hI.to x)
    change (F.map (hI.to x).right).hom = _
    rw [hx]
  rw [← e]
  exact gl_res_one _ s h

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.glue : ∀ d n : ℕ, ∃ N : ℕ, ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E] {E₀ : Type u''} [Category.{v''} E₀] (F : C ⥤ ModuleCat.{w} R) (G : E ⥤ C) (j : E₀ ⥤ E) [j.Full] [j.Faithful] (U : UF C) (D : C) (A : Act (𝟭 C) U d D) (L : Line (𝟭 C) U) (U' : UF E) (D' : E) (A' : Act j U' d D') (L' : Line j U') (θ : D ⟶ G.obj D') (h : ∀ a, (A.γ a : D ⟶ D) ≫ θ = θ ≫ G.map (A'.γ a)) (s : R), (∀ T, Acyc1 s (F.map (L.i.app T)).hom (F.map (L.γ.app T)).hom) → Desc s (G ⋙ F) j → (∀ T, Acyc1 s ((G ⋙ F).map (L'.i.app T)).hom ((G ⋙ F).map (L'.γ.app T)).hom) → NI s (Functor.whiskerRight (⟨fun _ => θ, fun _ _ a => h a⟩ : A.ι ⟶ A'.ι ⋙ G) F) → RI (s ^ N) n F (j ⋙ G) := by
  intro d n
  obtain ⟨N₁, h₁⟩ := CrystallineSemistableComparison.B.P.tors.{w, v, u, v, u} d n
  obtain ⟨N₂, h₂⟩ := CrystallineSemistableComparison.B.P.tors.{w, v', u', v'', u''} d n
  refine ⟨N₂ + (N₁ + 2) + (2 * n + 3), ?_⟩
  intro R _ C _ E _ E₀ _ F G j _ _ U D A L U' D' A' L' θ h s hL hD hL' hN
  let θn : A.ι ⟶ A'.ι ⋙ G := ⟨fun _ => θ, fun _ _ a => h a⟩
  have t1 : RI (s ^ N₁) n F A.ι := h₁ F (𝟭 C) U D A L s (gl_desc_id F s) hL
  have t2 : RI (s ^ N₂) n (G ⋙ F) A'.ι := h₂ (G ⋙ F) j U' D' A' L' s hD hL'
  have t3 : RI (s ^ N₁ * s ^ 2) n F (A'.ι ⋙ G) := by
    intro i hi
    have hp : (Mor.restrict F (A'.ι ⋙ G)).pull i =
        ((Mor.ofNatTrans (Functor.whiskerRight θn F)).pull i).comp ((Mor.restrict F A.ι).pull i) := by
      rw [← rc_pull_comp]
      exact (LinearMap.ext fun x => CrystallineSemistableComparison.P.prism ((Mor.restrict F A.ι).comp (Mor.ofNatTrans (Functor.whiskerRight θn F)))
        (Mor.restrict F (A'.ι ⋙ G)) θn (fun T x => rfl) i x).symm
    rw [hp]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).1 (t1 i hi) (P.ni_coh s (Functor.whiskerRight θn F) hN n i hi)
  have t4 : RI (s ^ N₂ * (s ^ N₁ * s ^ 2)) n F G := (P.ri_calc F G A'.ι _ _ n).2.2.1 t2 t3
  have t5 : RI (s ^ (2 * n + 3)) n (G ⋙ F) j := P.fib (Mor.restrict (G ⋙ F) j) s hD n
  have t6 := (P.ri_calc F G j _ _ n).1 t4 t5
  have he : s ^ (N₂ + (N₁ + 2) + (2 * n + 3)) = s ^ N₂ * (s ^ N₁ * s ^ 2) * s ^ (2 * n + 3) := by ring
  rw [he]
  exact t6
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

abbrev ChI (A : Type) : Type := {S : Set A // S.Nonempty}

def chPi {C : Type u} [Category.{v} C] {A : Type} (Q : A → C → Prop)
    (hQ : ∀ α ⦃T T' : C⦄, (T ⟶ T') → Q α T → Q α T') (hA : ∀ T, ∃ α, Q α T) : C ⥤ ChI A where
  obj T := ⟨{α | Q α T}, hA T⟩
  map f := homOfLE (show _ ≤ _ from fun α h => hQ α f h)

def chPhi {C : Type u} [Category.{v} C] {C₁ : Type u'} [Category.{v'} C₁] {A : Type} (P : C ⥤ ChI A)
    (S : ChI A) (ι : C₁ ⥤ C) (hm : ∀ T, S.1 ⊆ (P.obj (ι.obj T)).1) : C₁ ⥤ StructuredArrow S P :=
  Functor.toStructuredArrow ι S P (fun T => homOfLE (show S ≤ _ from hm T)) (fun _ => Subsingleton.elim _ _)

lemma chPhi_equiv {C : Type u} [Category.{v} C] {C₁ : Type u'} [Category.{v'} C₁] {A : Type} (P : C ⥤ ChI A)
    (S : ChI A) (ι : C₁ ⥤ C) (hO : Onto ι (fun T => S.1 ⊆ (P.obj T).1)) :
    (chPhi P S ι hO.mem).IsEquivalence := by
  have := hO.full
  have := hO.faithful
  have : (chPhi P S ι hO.mem).Full :=
    ⟨fun {X Y} f => ⟨ι.preimage f.right, StructuredArrow.hom_ext _ _ (ι.map_preimage f.right)⟩⟩
  have : (chPhi P S ι hO.mem).Faithful :=
    ⟨fun {X Y} f g h => ι.map_injective (congrArg (fun k => CommaMorphism.right k) h)⟩
  have : (chPhi P S ι hO.mem).EssSurj := ⟨fun X => by
    obtain ⟨T₁, ⟨e⟩⟩ := hO.ess X.right (leOfHom X.hom)
    exact ⟨T₁, ⟨StructuredArrow.isoMk e (Subsingleton.elim _ _)⟩⟩⟩
  exact {}

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.chart : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) {A : Type} (Q : A → C → Prop) (s : R) (n : ℕ), (∀ α ⦃T T' : C⦄, (T ⟶ T') → Q α T → Q α T') → (∀ T, ∃ α, Q α T) → (∀ S : Set A, S.Nonempty → ∃ (C₁ : Type u) (_ : Category.{v} C₁) (C₁' : Type u') (_ : Category.{v'} C₁') (ι : C₁ ⥤ C) (ι' : C₁' ⥤ C') (G₁ : C₁' ⥤ C₁), Onto ι (fun T => ∀ α ∈ S, Q α T) ∧ Onto ι' (fun T => ∀ α ∈ S, Q α (G.obj T)) ∧ Nonempty (G₁ ⋙ ι ≅ ι' ⋙ G) ∧ RI s (n + 1) (ι ⋙ F) G₁) → RI (s ^ (2 * n + 3)) n F G := by
  intro R _ C _ C' _ F G A Q s n hQ hA hS
  let π := chPi Q hQ hA
  have key : ∀ S : ChI A, RI s (n + 1) (StructuredArrow.proj S π ⋙ F) (StructuredArrow.pre S G π) := by
    intro S
    obtain ⟨C₁, _, C₁', _, ι, ι', G₁, hO, hO', ⟨e⟩, hR⟩ := hS S.1 S.2
    have hO2 : Onto ι (fun T => S.1 ⊆ (π.obj T).1) := hO
    have hO2' : Onto ι' (fun T => S.1 ⊆ ((G ⋙ π).obj T).1) := hO'
    let Φ := chPhi π S ι hO2.mem
    let Φ' := chPhi (G ⋙ π) S ι' hO2'.mem
    let X := StructuredArrow.proj S π ⋙ F
    have h1 : RI 1 (n + 1) X Φ := (P.ri_calc X Φ (𝟭 _) 1 1 (n + 1)).2.2.2.2.2.1 (chPhi_equiv π S ι hO2)
    have h2 : RI s (n + 1) (Φ ⋙ X) G₁ := hR
    have h3 : RI (1 * s) (n + 1) X (G₁ ⋙ Φ) := (P.ri_calc X Φ G₁ 1 s (n + 1)).1 h1 h2
    have iso : G₁ ⋙ Φ ≅ Φ' ⋙ StructuredArrow.pre S G π :=
      NatIso.ofComponents (fun T => StructuredArrow.isoMk (e.app T) (Subsingleton.elim _ _))
        (fun f => StructuredArrow.hom_ext _ _ (e.hom.naturality f))
    have h4 : RI (1 * s) (n + 1) X (Φ' ⋙ StructuredArrow.pre S G π) :=
      (P.ri_calc X (G₁ ⋙ Φ) (𝟭 _) (1 * s) 1 (n + 1)).2.2.2.2.1 _ iso h3
    have h5 : RI 1 (n + 1) (StructuredArrow.pre S G π ⋙ X) Φ' :=
      (P.ri_calc (StructuredArrow.pre S G π ⋙ X) Φ' (𝟭 _) 1 1 (n + 1)).2.2.2.2.2.1 (chPhi_equiv (G ⋙ π) S ι' hO2')
    have h6 := (P.ri_calc X (StructuredArrow.pre S G π) Φ' 1 (1 * s) (n + 1)).2.2.1 h5 h4
    rwa [one_mul, one_mul] at h6
  intro j hj
  have h := CrystallineSemistableComparison.P.rel π (Mor.restrict F G) s j (fun S q hq => key S q (by omega))
  have he : s ^ (2 * n + 3) = s ^ (2 * j + 3) * s ^ (2 * (n - j)) := by
    rw [← pow_add]; congr 1; omega
  rw [he]
  exact (CrystallineSemistableComparison.P.upTo_alg _ LinearMap.id _ _).2.2.2.1 h
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

lemma gl_onto {D : Type u} [Category.{v} D] {D₁ : Type u'} [Category.{v'} D₁] (Z : ObjectProperty D)
    (κ : D₁ ⥤ D) (hκ : ∀ T, Z (κ.obj T)) (W : D → Prop) (h : Onto κ W) :
    Onto (Z.lift κ hκ) (fun T => W T.obj) := by
  have : κ.Full := h.full
  have : κ.Faithful := h.faithful
  have : (Z.lift κ hκ ⋙ Z.ι).Full := h.full
  have : (Z.lift κ hκ ⋙ Z.ι).Faithful := h.faithful
  refine ⟨Functor.Full.of_comp_faithful _ Z.ι, Functor.Faithful.of_comp _ Z.ι, fun T => h.mem T, ?_⟩
  intro T hT
  obtain ⟨T₁, ⟨f⟩⟩ := h.ess T.obj hT
  exact ⟨T₁, ⟨Z.ι.preimageIso f⟩⟩

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.glob : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) {A : Type} (Q : A → C → Prop) (s : R) (n : ℕ), (∀ α ⦃T T' : C⦄, (T ⟶ T') → Q α T → Q α T') → RI 1 n F (ObjectProperty.ι fun T => ∃ α, Q α T) → RI 1 n (G ⋙ F) (ObjectProperty.ι fun T => ∃ α, Q α (G.obj T)) → (∀ S : Set A, S.Nonempty → ∃ (C₁ : Type u) (_ : Category.{v} C₁) (C₁' : Type u') (_ : Category.{v'} C₁') (ι : C₁ ⥤ C) (ι' : C₁' ⥤ C') (G₁ : C₁' ⥤ C₁), Onto ι (fun T => ∀ α ∈ S, Q α T) ∧ Onto ι' (fun T => ∀ α ∈ S, Q α (G.obj T)) ∧ Nonempty (G₁ ⋙ ι ≅ ι' ⋙ G) ∧ RI s (n + 1) (ι ⋙ F) G₁) → RI (s ^ (2 * n + 3)) n F G := by
  intro R _ C _ C' _ F G A Q s n hQ hP hP' hS
  let Pr : ObjectProperty C := fun T => ∃ α, Q α T
  let Pr' : ObjectProperty C' := fun T => ∃ α, Q α (G.obj T)
  let Gq : Pr'.FullSubcategory ⥤ Pr.FullSubcategory := Pr.lift (Pr'.ι ⋙ G) (fun T => T.property)
  let Fq : Pr.FullSubcategory ⥤ ModuleCat.{w} R := Pr.ι ⋙ F
  have hc : RI (s ^ (2 * n + 3)) n Fq Gq := by
    refine P.chart Fq Gq (fun α T => Q α T.obj) s n (fun α T T' f h => hQ α f.hom h) (fun T => T.property) ?_
    intro S hSn
    obtain ⟨C₁, _, C₁', _, ι, ι', G₁, hO, hO', ⟨e⟩, hR⟩ := hS S hSn
    obtain ⟨α₀, hα₀⟩ := hSn
    let ιq : C₁ ⥤ Pr.FullSubcategory := Pr.lift ι (fun T => ⟨α₀, hO.mem T α₀ hα₀⟩)
    let ιq' : C₁' ⥤ Pr'.FullSubcategory := Pr'.lift ι' (fun T => ⟨α₀, hO'.mem T α₀ hα₀⟩)
    refine ⟨C₁, inferInstance, C₁', inferInstance, ιq, ιq', G₁, ?_, ?_, ?_, hR⟩
    · exact gl_onto Pr ι _ (fun T => ∀ α ∈ S, Q α T) hO
    · exact gl_onto Pr' ι' _ (fun T => ∀ α ∈ S, Q α (G.obj T)) hO'
    · exact ⟨Functor.fullyFaithfulCancelRight Pr.ι e⟩
  have h1 : RI (1 * s ^ (2 * n + 3)) n F (Gq ⋙ Pr.ι) := (P.ri_calc F Pr.ι Gq 1 _ n).1 hP hc
  have h2 : RI (1 * (1 * s ^ (2 * n + 3))) n F G := (P.ri_calc F G Pr'.ι 1 _ n).2.2.1 hP' h1
  rwa [one_mul, one_mul] at h2
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.line_univ : ∀ {C : Type u} [Category.{v} C] (U : UF C) (P : ∀ ⦃T T' : C⦄, (T ⟶ T') → (T' ⟶ T') → Prop), (∀ T : C, ∃ (T₁ : C) (i : T ⟶ T₁) (η : U.U T₁), (∀ (T' : C) (φ : T ⟶ T') (a : U.U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ U.map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → U.map g η = U.q _ * η → P i g) → ∃ L : Line (𝟭 C) U, ∀ T, P (L.i.app T) (L.γ.app T) :=
  @GlobalTheory.CompanionTheory.LineUniv.exists_line
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.rees_up : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n : ℕ), ((∀ r, RI 1 n (Φ.S r).fn G) → RI 1 n Φ.rees G) ∧ (∀ μ' ξ : R, Φ.μ = μ' * ξ → (∀ r T x, x ∈ (Φ.S r).S T → ξ • x ∈ (Φ.S (r + 1)).S T) → (∀ r, Desc μ' (Φ.S r).fn G) → Desc (X : ℤ[X]) Φ.rees G) ∧ ∀ {T T' : C} (i : T ⟶ T') (g : T' ⟶ T'), Φ.FAcyc i g → Acyc1 (X : ℤ[X]) (Φ.rees.map i).hom (Φ.rees.map g).hom :=
  @GlobalTheory.CompanionTheory.ReesUp.main
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

theorem CrystallineSemistableComparison.B.P.rees_down : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n N : ℕ), (∀ T, (Φ.S 0).S T = ⊤) → RI ((X : ℤ[X]) ^ N) n Φ.rees G → ∀ j ≤ n, InjUpTo (Φ.μ ^ N) ((Mor.restrict F G).pull j) ∧ ∀ y, ∃ x ∈ (Φ.S N).img j, (Mor.restrict F G).pull j x = Φ.μ ^ N • y :=
  @GlobalTheory.CompanionTheory.ReesDown.main
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris

namespace CrystallineSemistableComparison.B

open PAlg CH

theorem exists_dp {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) (h : i.Flat) (I : Ideal Λ) (γ : DividedPowers I) :
    ∃ δ : DividedPowers (I.map i), IsDPMorphism γ δ i := by
  let _ := i.toAlgebra
  have : Module.Flat Λ D := h
  exact GlobalTheory.CompanionTheory.JLiftDP.dpFlat Λ D I γ

variable {l : ℕ} [Fact l.Prime]

theorem local_of (hD : D.Out l) : Local l := by
  intro d j
  obtain ⟨N, hN⟩ := P.glue.{0, 0, 1, 0, 1, 0, 1} d j
  refine ⟨N, fun {O} _ F κ ε k n ρ hρ hn hk s => ?_⟩
  obtain ⟨𝓛⟩ := P.elift s.a (fun k => (s.T k : s.R)) (bs l k n).I (κb κ k n) s.et
  obtain ⟨δ, hδ⟩ := exists_dp 𝓛.i (P.lift_flat 𝓛.i 𝓛.t 𝓛.et).1 (bs l k n).I (bs l k n).γ
  have hp : (bs l k n).p ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hnil : IsNilpotent ((bs l k n).p : (bs l k n).R) := ⟨n, (base l).pow_l_acr n⟩
  obtain ⟨𝒯⟩ := P.tower_ex κ s
  obtain ⟨A, hA⟩ := P.thick_act s (b := bs l k n) rfl 𝓛 δ hδ hp hnil (ε.qU n) (ε.qU_mem k n)
  obtain ⟨A', hA'⟩ := P.tower_act 𝒯 ε
  obtain ⟨θ, hθ, hθγ⟩ := P.theta_ex 𝒯 k n 𝓛 δ hδ hp hnil ε A A' hA hA'
  have hε := P.eps_facts ε
  have hq : (ε.qU n : (bs l k n).R) = (base l).cris n (ε.qk 1) ^ (bs l k n).p :=
    (ε.qU_val n).trans ((congrArg ((base l).cris n) (hε.2.1 0).symm).trans (map_pow _ _ _))
  have hμ : (base l).cris n ε.μ = (ε.qU n : (bs l k n).R) - 1 := by
    rw [Eps.μ, map_sub, map_one, ε.qU_val]
  have hξ : (∑ i ∈ Finset.range (bs l k n).p, (base l).cris n (ε.qk 1) ^ i) ∈ (bs l k n).I := by
    have := fil_le k (base l) n (hε.2.2.1 (base l) n)
    simpa only [map_sum, map_pow] using this
  obtain ⟨L, hL⟩ := P.line_univ (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)) (fun _ _ i g => (flt F κ ε k n ρ hρ).FAcyc i g)
    (P.thick_line F (bs l k n) rfl (κb κ k n) ((base l).cris n) ρ hρ ε.μ (ε.μ_mem k (base l) n) (ε.qU n) (ε.qU_mem k n)
      ((base l).cris n (ε.qk 1)) Fact.out hq hμ hξ)
  obtain ⟨L', hL'⟩ := P.cont_line F κ ε k n ρ hρ
  obtain ⟨ni⟩ := P.local_ni 𝒯 k n 𝓛 δ hδ hp hnil ε ρ hρ A.γ A'.γ ⟨fun _ => θ, fun _ _ a => hθγ a⟩ hn hθ
    (fun a j => (hA _ _ (𝟙 _) j).trans (congrArg (· * 𝓛.t j) (Units.val_pow_eq_pow_val _ _)))
    (fun a j => (hA' _ _ (𝟙 _) j).trans (congrArg (· * (𝒯.c j 0).val) (Units.val_pow_eq_pow_val _ _)))
  exact hN (flt F κ ε k n ρ hρ).rees (gE F κ k n) (jE _) _ _ A L _ _ A' L' θ hθγ _
    (fun T => (P.rees_up (flt F κ ε k n ρ hρ) (𝟭 _) 0).2.2 _ _ (hL T)) (P.desc hD F κ ε k n ρ hρ hk)
    (fun T => (P.rees_up ((flt F κ ε k n ρ hρ).comap (gE F κ k n)) (𝟭 _) 0).2.2 _ _ (hL' T)) ni

theorem ri_pow {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R} {G : C' ⥤ C}
    {s : R} {a b n : ℕ} (h : a ≤ b) (H : RI (s ^ a) n F G) : RI (s ^ b) n F G := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  exact (P.ri_calc F G (𝟭 _) _ _ n).2.2.2.1 H

theorem global_of (h : Local l) (d j : ℕ) : ∃ N : ℕ, ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), n ≠ 0 → (k = false ∨ ρ = 0) → F.Atlas d →
    RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε k n ρ hρ).rees (gT F κ k n) := by
  choose N hN using fun d' => h d' (j + 1)
  refine ⟨((Finset.range (d + 1)).sup N) * (2 * j + 3), fun {O} _ F κ ε k n ρ hρ hn hk 𝒜 => ?_⟩
  rw [pow_mul]
  have hp : (bs l k n).p ≠ 0 := (Fact.out : l.Prime).ne_zero
  have z₁ := fun r => P.thick_zar F (bs l k n) rfl (κb κ k n) ((base l).cris n) 𝒜 hp r
  have z₂ := fun r => P.el_zar F κ 𝒜 k n r
  have onto : ∀ {C : Type 1} [Category.{0} C] (Q : C → Prop), Onto (ObjectProperty.ι Q) Q := fun Q =>
    ⟨inferInstance, inferInstance, fun T => T.property, fun T hT => ⟨⟨T, hT⟩, ⟨Iso.refl _⟩⟩⟩
  refine P.glob _ (gT F κ k n) (fun α T => (𝒜.V α).In T.y.1.2) _ j ?_ ?_ ?_ fun S hS => ?_
  · intro α T T' φ hT
    have e : F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) T.y.1.2 = T'.y.1.2 :=
      congrArg (fun z => z.1.2) φ.pt
    exact e ▸ (𝒜.V α).in_map _ hT
  · exact (P.rees_up (flt F κ ε k n ρ hρ) _ j).1 fun r => P.zar _ _ _ (onto _) (z₁ (ρ r)) j
  · exact (P.rees_up ((flt F κ ε k n ρ hρ).comap (gT F κ k n)) _ j).1 fun r => P.zar _ _ _ (onto _) (z₂ (ρ r)) j
  · obtain ⟨d', hd', ⟨s⟩⟩ := 𝒜.small S hS
    refine ⟨_, _, _, _, subThick (Fn.Sub.inter 𝒜.V S) (bs l k n) rfl (κb κ k n), subEl κ (Fn.Sub.inter 𝒜.V S),
      gT (Fn.Sub.inter 𝒜.V S).fn κ k n, P.thick_onto _ _ _ _, P.el_onto F κ 𝒜 S k n hn, ⟨eqToIso (subEl_gT κ _ k n)⟩, ?_⟩
    rw [subThick_rees]
    exact ri_pow (Finset.le_sup (f := N) (Finset.mem_range.2 (Nat.lt_succ_of_le hd'))) (hN d' _ κ ε k n ρ hρ hn hk s)

theorem pull_factor {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R}
    {F' : C' ⥤ ModuleCat.{0} R} (m : Mor F F' (RingHom.id R)) (h : ∀ T, Function.Bijective (m.τ T)) (j : ℕ) :
    ∃ e : H (m.G ⋙ F) j →ₗ[R] H F' j, Function.Bijective e ∧ ∀ x, m.pull j x = e ((Mor.restrict F m.G).pull j x) := by
  let m' : Mor (m.G ⋙ F) F' (RingHom.id R) := ⟨𝟭 _, m.τ, m.nat⟩
  have : m'.G.IsLeftAdjoint := inferInstanceAs (𝟭 C').IsLeftAdjoint
  exact ⟨m'.pull j, CrystallineSemistableComparison.P.adj_mor m' h j, fun x => (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F m.G) m' j x).1⟩

theorem transfer {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R}
    {F' : C' ⥤ ModuleCat.{0} R} (m : Mor F F' (RingHom.id R)) (h : ∀ T, Function.Bijective (m.τ T)) (j : ℕ) (s : R)
    (S : Submodule R (H F j)) (H₁ : InjUpTo s ((Mor.restrict F m.G).pull j))
    (H₂ : ∀ y, ∃ x ∈ S, (Mor.restrict F m.G).pull j x = s • y) :
    UpTo s (m.pull j) ∧ ∀ y, ∃ x ∈ S, m.pull j x = s • y := by
  obtain ⟨e, he, hm⟩ := pull_factor m h j
  have h2 : ∀ y, ∃ x ∈ S, m.pull j x = s • y := fun y => by
    obtain ⟨y', rfl⟩ := he.2 y
    obtain ⟨x, hx, e'⟩ := H₂ y'
    exact ⟨x, hx, by rw [hm, e', map_smul]⟩
  refine ⟨⟨fun x hx => H₁ x (he.1 ?_), fun y => (h2 y).imp fun _ hx => hx.2⟩, h2⟩
  rw [← hm, hx, map_zero]

theorem subsingleton_H {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    (h : ∀ T, Subsingleton (F.obj T)) (j : ℕ) : Subsingleton (H F j) := by
  have : Subsingleton (Cn F j) := ⟨fun _ _ => funext fun _ => (h _).elim _ _⟩
  exact Submodule.Quotient.mk_surjective _ |>.subsingleton

theorem acr_zero (A : PAlg l) : Subsingleton (A.Acr 0) := subsingleton_of_zero_eq_one (by simpa using (A.pow_l_acr 0).symm)

theorem upTo_zero {R M N : Type _} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (h₁ : Subsingleton M)
    (h₂ : Subsingleton N) (f : M →ₗ[R] N) (s : R) (S : Submodule R M) : UpTo s f ∧ ∀ y, ∃ x ∈ S, f x = s • y :=
  ⟨⟨fun _ _ => h₁.elim _ _, fun _ => ⟨0, h₂.elim _ _⟩⟩, fun _ => ⟨0, zero_mem _, h₂.elim _ _⟩⟩

theorem om_zero {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (h : Subsingleton b.R) (j : ℕ) :
    Subsingleton (H (OM L c) j) :=
  subsingleton_H _ (fun T => (show Subsingleton T.B from T.i.codomain_trivial)) j

theorem pdFlt_zero {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ)
    (hμ : c μ ∈ b.I) (T : Thick L) : ((pdFlt L c ρ hρ μ hμ).S 0).S T = ⊤ := eq_top_iff.2 fun x _ => by
  change (show T.B from x) ∈ T.pdPow (ρ 0)
  rw [hρ.1, T.pdPow_zero]; trivial

theorem level_zero {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (j : ℕ) (s : Acris l)
    (S : Submodule (Acris l) (Hc F κ k 0 j)) : UpTo s (β F κ k 0 j) ∧ ∀ y, ∃ x ∈ S, β F κ k 0 j x = s • y :=
  upTo_zero (om_zero (Lc F κ k 0) ((base l).cris 0) (acr_zero (base l)) j)
    (subsingleton_H (modF (AcrEl (F.pt κ) 0)) (fun T => acr_zero T.1.obj) j) (β F κ k 0 j) s S

theorem level_pos {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n j N : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)
    (h : RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε k n ρ hρ).rees (gT F κ k n)) :
    UpTo (ε.μ ^ N) (β F κ k n j) ∧ ∀ y, ∃ x ∈ HcFil F κ k n (ρ N) j, β F κ k n j x = ε.μ ^ N • y :=
  have H := P.rees_down (flt F κ ε k n ρ hρ) (gT F κ k n) j N (pdFlt_zero _ _ ρ hρ _ _) h j le_rfl
  transfer (βMor F κ k n) (fun _ => Function.bijective_id) j (ε.μ ^ N) (HcFil F κ k n (ρ N) j) H.1 H.2

theorem slow_zero : Slow 0 := ⟨rfl, fun _ => Nat.zero_le _⟩

theorem slow_id : Slow id := ⟨rfl, fun _ => le_rfl⟩

theorem level_all {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n j N : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)
    (h : n ≠ 0 → RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε k n ρ hρ).rees (gT F κ k n)) :
    UpTo (ε.μ ^ N) (β F κ k n j) ∧ ∀ y, ∃ x ∈ HcFil F κ k n (ρ N) j, β F κ k n j x = ε.μ ^ N • y :=
  match n, h with
  | 0, _ => level_zero F κ k j _ _
  | n + 1, h => level_pos F κ ε k (n + 1) j N ρ hρ (h n.succ_ne_zero)

theorem main_of (hD : D.Out l) : Main l := fun d j =>
  (global_of (local_of hD) d j).imp fun N hN {_} _ F κ ε 𝒜 n =>
    ⟨fun k => (level_all F κ ε k n j N 0 slow_zero fun hn => hN F κ ε k n 0 slow_zero hn (Or.inr rfl) 𝒜).1,
      (level_all F κ ε false n j N id slow_id fun hn => hN F κ ε false n id slow_id hn (Or.inl rfl) 𝒜).2⟩

end CrystallineSemistableComparison.B
end
end
