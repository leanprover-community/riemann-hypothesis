import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDualOfAffinePairing

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen GlobalTheory.CurveRootGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoSeq

section General

variable {O : Type} [CommRing O] {X T T' S : Scheme.{0}} {A B A' B' : X.Modules}

def sqIso {b : S ⟶ T} {a : T ⟶ X} {c : S ⟶ T'} {a' : T' ⟶ X} (w : b ≫ a = c ≫ a') :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b ≅ Scheme.Modules.pullback a' ⋙ Scheme.Modules.pullback c :=
  Scheme.Modules.pullbackComp b a ≪≫ Scheme.Modules.pullbackCongr w ≪≫ (Scheme.Modules.pullbackComp c a').symm

structure Datum (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ) where

  D : X.Modules

  ρ : O →+* End D

  a : A ⟶ D

  b : D ⟶ B

  u : A' ⟶ D

  v : D ⟶ B'
  w₁ : a ≫ b = 0
  w₂ : u ≫ v = 0
  isVB : IsVB D r
  exact₁ : (ShortComplex.mk a b w₁).ShortExact
  exact₂ : (ShortComplex.mk u v w₂).ShortExact
  equiv_a : IsEquivariant α ρ a
  equiv_b : IsEquivariant ρ β b
  equiv_u : IsEquivariant α' ρ u
  equiv_v : IsEquivariant ρ β' v

variable (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ)

abbrev DatumOn (f : T ⟶ X) : Type 1 := Datum (pullAct α f) (pullAct β f) (pullAct α' f) (pullAct β' f) r

variable {α β α' β' r}

def Agree {a : T ⟶ X} {a' : T' ⟶ X} (d : DatumOn α β α' β' r a) (d' : DatumOn α β α' β' r a') {b : S ⟶ T} {c : S ⟶ T'}
    (w : b ≫ a = c ≫ a') (φ : (Scheme.Modules.pullback b).obj d.D ≅ (Scheme.Modules.pullback c).obj d'.D) : Prop :=
  IsEquivariant (pullAct d.ρ b) (pullAct d'.ρ c) φ.hom ∧
    (Scheme.Modules.pullback b).map d.a ≫ φ.hom = (sqIso w).hom.app A ≫ (Scheme.Modules.pullback c).map d'.a ∧
    φ.hom ≫ (Scheme.Modules.pullback c).map d'.b = (Scheme.Modules.pullback b).map d.b ≫ (sqIso w).hom.app B ∧
    (Scheme.Modules.pullback b).map d.u ≫ φ.hom = (sqIso w).hom.app A' ≫ (Scheme.Modules.pullback c).map d'.u ∧
    φ.hom ≫ (Scheme.Modules.pullback c).map d'.v = (Scheme.Modules.pullback b).map d.v ≫ (sqIso w).hom.app B'

def RestrictsTo (d : Datum α β α' β' r) {a : T ⟶ X} (d' : DatumOn α β α' β' r a)
    (e : (Scheme.Modules.pullback a).obj d.D ≅ d'.D) : Prop :=
  IsEquivariant (pullAct d.ρ a) d'.ρ e.hom ∧
    (Scheme.Modules.pullback a).map d.a ≫ e.hom = d'.a ∧ e.hom ≫ d'.b = (Scheme.Modules.pullback a).map d.b ∧
    (Scheme.Modules.pullback a).map d.u ≫ e.hom = d'.u ∧ e.hom ≫ d'.v = (Scheme.Modules.pullback a).map d.v

def biprodAct (α : O →+* End A) (β : O →+* End B) : O →+* End (A ⊞ B) where
  toFun x := biprod.map (act α x) (act β x)
  map_one' := by
    rw [act, act, map_one, map_one]
    exact biprod.hom_ext _ _ (by simp [End.one_def]) (by simp [End.one_def])
  map_mul' x y := by
    rw [act, act, map_mul, map_mul]
    exact biprod.hom_ext _ _ (by simp [End.mul_def]) (by simp [End.mul_def])
  map_zero' := by
    rw [act, act, map_zero, map_zero]
    change (biprod.map (0 : A ⟶ A) (0 : B ⟶ B) : A ⊞ B ⟶ A ⊞ B) = (0 : A ⊞ B ⟶ A ⊞ B)
    exact biprod.hom_ext _ _ (by simp) (by simp)
  map_add' x y := by
    rw [act, act, map_add, map_add]
    change (biprod.map (act α x + act α y) (act β x + act β y) : A ⊞ B ⟶ A ⊞ B) =
      (biprod.map (act α x) (act β x) + biprod.map (act α y) (act β y) : A ⊞ B ⟶ A ⊞ B)
    exact biprod.hom_ext _ _ (by simp) (by simp)

def Datum.split (α : O →+* End A) (β : O →+* End B) {m n : ℕ} (hA : IsVB A m) (hB : IsVB B n) :
    Datum α β β α (m + n) where
  D := A ⊞ B
  ρ := biprodAct α β
  a := biprod.inl
  b := biprod.snd
  u := biprod.inr
  v := biprod.fst
  w₁ := by simp
  w₂ := by simp
  isVB := hA.biprod hB
  exact₁ := (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
  exact₂ := (ShortComplex.Splitting.mk (S := ShortComplex.mk (biprod.inr : B ⟶ A ⊞ B) biprod.fst (by simp))
    biprod.snd biprod.inl (by simp) (by simp) (by rw [add_comm]; exact biprod.total)).shortExact
  equiv_a x := by simp [act, biprodAct]
  equiv_b x := by simp [act, biprodAct]
  equiv_u x := by simp [act, biprodAct]
  equiv_v x := by simp [act, biprodAct]

example (X : Scheme.{0}) :
    let σ := scalarAct (GlobalTheory.QCoh.freeModule X (Fin 1)) (RingHom.id Γ(X, ⊤))
    Nonempty (Datum σ σ σ σ 2) :=
  ⟨Datum.split _ _ (isVB_freeModule_fin X 1) (isVB_freeModule_fin X 1)⟩

end General

section Dieu

variable {O : Type} [CommRing O] (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}}
  [Algebra k Γ(C, ⊤)] {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

abbrev DieuDatum (g : ℕ) : Type 1 :=
  Datum (omegaAct i) ((lieAct i).comp c) (pullAct ((lieAct i).comp c) (frob C q (natCast_eq_zero C q k)))
    (pullAct (omegaAct i) (frob C q (natCast_eq_zero C q k))) (2 * g)

abbrev DieuDatumOn (g : ℕ) {T : Scheme.{0}} (f : T ⟶ C) : Type 1 :=
  DatumOn (omegaAct i) ((lieAct i).comp c) (pullAct ((lieAct i).comp c) (frob C q (natCast_eq_zero C q k)))
    (pullAct (omegaAct i) (frob C q (natCast_eq_zero C q k))) (2 * g) f

theorem hasDieu_iff : HasDieu q k c i ↔ ∃ g, IsVB (omega G) g ∧ Nonempty (DieuDatum q k c i g) :=
  ⟨fun ⟨D, g, ρ, a, b, u, v, w₁, w₂, h, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ =>
      ⟨g, h, ⟨⟨D, ρ, a, b, u, v, w₁, w₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩⟩⟩,
    fun ⟨g, h, ⟨d⟩⟩ => ⟨d.D, g, d.ρ, d.a, d.b, d.u, d.v, d.w₁, d.w₂, h, d.isVB, d.exact₁, d.exact₂, d.equiv_a,
      d.equiv_b, d.equiv_u, d.equiv_v⟩⟩

end Dieu

end GlobalTheory.TwoSeq
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDatum

variable {O : Type} [CommRing O]

section Abelian

variable {T : Scheme.{0}} {A : Over T} [GrpObj A]

def IsSelfDual (c : O →+* O) (i : OAct O A) (P : LB (A ⊗ A).left) : Prop :=
  IsDual A A P ∧ LBIso (swap P) P ∧
    ∀ x, LBIso (ev P (fst A A ≫ i.act x) (snd A A)) (ev P (fst A A) (snd A A ≫ i.act (c x)))

def actPull (i : OAct O A) (x : O) {V : T.Opens} (hV : IsAffineOpen V) :
    primDR (onAff A hV) →ₗ[Γ(T, V)] primDR (onAff A hV) :=
  haveI := i.hom x
  primPull (dp0 Γ(T, V)) (𝟙 _) (A := onAff A hV) (B := onAff A hV) ((Over.pullback hV.fromSpec).map (i.act x))

variable {H : T.Modules} (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))

def IsDRAct (i : OAct O A) (ρ : O →+* End H) : Prop :=
  ∀ (x : O) (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
    e V hV ((VB.act ρ x).app V s) = actPull i x hV (e V hV s)

def IsHodgeIncl (a : omega A ⟶ H) : Prop :=
  ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(omega A, V)),
    e V hV (a.app V s) ∈ PrimitiveSubmodule (onAff A hV) ∧ HodgeSub.Corr A hV s (e V hV (a.app V s))

def IsPolPairing (P : LB (A ⊗ A).left) (β : H ⟶ dual H) : Prop :=
  ∀ (V : T.Opens) (hV : IsAffineOpen V),
    ∃ (m : (onAff A hV ⊗ onAff A hV).left ⟶ (A ⊗ A).left)
      (φ : HdR (onAff A hV) →ₗ[Γ(T, V)] HdR (onAff A hV) →ₗ[Γ(T, V)] Γ(T, V)),
      m ≫ (fst A A).left = (fst (onAff A hV) (onAff A hV)).left ≫ pullback.fst A.hom hV.fromSpec ∧
      m ≫ (snd A A).left = (snd (onAff A hV) (onAff A hV)).left ≫ pullback.fst A.hom hV.fromSpec ∧
      IsCorrForm (dp0 Γ(T, V)) (𝟙 _) (onAff A hV) (onAff A hV) (P.pull m) φ ∧ φ.IsPerfPair ∧
      ∀ (s : Γ(H, V)) (x y : HdR (onAff A hV)), (∀ t, x (e V hV t) = dualApp (β.app V s) le_rfl t) →
        φ x y = y (e V hV s)

variable (p : ℕ) [Fact p.Prime] (h0 : (p : Γ(T, ⊤)) = 0)

def IsLinFrob (Ψ : (frobPull p h0).obj H ⟶ H) : Prop :=
  ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
    e V hV (Ψ.app V (QCoh.pullbackSections (frob T p h0) H (le_refl V) s)) =
      ConjSeq.frobDR p Γ(T, V) (SS.FrobField.cast_zero h0 V) (onAff A hV) (e V hV s)

omit e in

def IsDRDatum (i : OAct O A) (P : LB (A ⊗ A).left) (ρ : O →+* End H) (a : omega A ⟶ H) (b : H ⟶ Lie A)
    (u : (frobPull p h0).obj (Lie A) ⟶ H) (v : H ⟶ (frobPull p h0).obj (omega A)) : Prop :=
  ∃ (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)) (β : H ⟶ dual H)
    (Ψ : (frobPull p h0).obj H ⟶ H),
    IsDRIso A H e ∧ IsDRAct e i ρ ∧ IsHodgeIncl e a ∧ IsPolPairing e P β ∧ IsLinFrob e p h0 Ψ ∧
    b = β ≫ dualMap a ∧ (frobPull p h0).map b ≫ u = Ψ ∧
    v ≫ (frobPull p h0).map (cartierDualToBidual (omega A)) ≫ DualPull.theta (frob T p h0) (Lie A) = β ≫ dualMap u

end Abelian

section Res

variable {S T : Scheme.{0}} {G : Over S} [GrpObj G] [QuasiSeparated G.hom] {A : Over T} [GrpObj A] {f : T ⟶ S}
  {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) (p : ℕ) [Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0)
  (hT : (p : Γ(T, ⊤)) = 0) {g : ℕ} (hg : IsVB (omega G) g)

def omegaRes : (Scheme.Modules.pullback f).obj (omega G) ≅ omega A := asIso (omegaBase h)

def lieRes : (Scheme.Modules.pullback f).obj (Lie G) ≅ Lie A := @asIso _ _ _ _ (lieBase h) (isIso_lieBase h hg)

def frobLieRes : (Scheme.Modules.pullback f).obj ((frobPull p hS).obj (Lie G)) ≅ (frobPull p hT).obj (Lie A) :=
  (frobPullPullbackIso p hS f hT).app (Lie G) ≪≫ (frobPull p hT).mapIso (lieRes h hg)

def frobOmegaRes : (Scheme.Modules.pullback f).obj ((frobPull p hS).obj (omega G)) ≅ (frobPull p hT).obj (omega A) :=
  (frobPullPullbackIso p hS f hT).app (omega G) ≪≫ (frobPull p hT).mapIso (omegaRes h)

end Res

section On

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C T : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G) {A : Over T} [GrpObj A] {f : T ⟶ C}
  {φ : A.left ⟶ G.left}

omit [Fact q.Prime] in
include k in

theorem cast_eq_zero (f : T ⟶ C) : (q : Γ(T, ⊤)) = 0 := SS.FrobField.cast_zero_of_hom f (natCast_eq_zero C q k)

def IsDRDatumOn (j : OAct O A) (h : IsGrpPullback A G f φ) (P : LB (A ⊗ A).left) {g : ℕ} (hg : IsVB (omega G) g)
    (d : TwoSeq.DieuDatumOn q k c i g f) : Prop :=
  IsDRDatum q (cast_eq_zero q k f) j P d.ρ ((omegaRes h).inv ≫ d.a) (d.b ≫ (lieRes h hg).hom)
    ((frobLieRes h q (natCast_eq_zero C q k) (cast_eq_zero q k f) hg).inv ≫ d.u)
    (d.v ≫ (frobOmegaRes h q (natCast_eq_zero C q k) (cast_eq_zero q k f)).hom)

end On

section Ext

variable {X : Scheme.{0}} {F G : X.Modules}

theorem hom_ext_affine {φ ψ : F ⟶ G}
    (h : ∀ (V : X.Opens), IsAffineOpen V → ∀ s : Γ(F, V), φ.app V s = ψ.app V s) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  refine QCoh.section_eq_of_cover _ (fun U : {U : X.Opens // IsAffineOpen U ∧ U ≤ W} ↦ U.1)
    (fun U ↦ U.2.2) ?_ _ _ fun U ↦ ?_
  · intro x hx
    obtain ⟨U, hU, hxU, hle⟩ := QCoh.exists_affine_mem_le x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hle⟩, hxU⟩
  · exact (QCoh.hom_app_res _ _ _).symm.trans ((h _ U.2.1 _).trans (QCoh.hom_app_res _ _ _))

theorem hom_dual_ext_affine {E : X.Modules} {φ ψ : E ⟶ dual F}
    (h : ∀ (V : X.Opens), IsAffineOpen V → ∀ (s : Γ(E, V)) (t : Γ(F, V)),
      dualApp (φ.app V s) le_rfl t = dualApp (ψ.app V s) le_rfl t) : φ = ψ := by
  refine hom_ext_affine fun V _ s ↦ dual_ext fun W hW t ↦ ?_
  refine AffinePairingGlue.fun_ext_affine fun U hU hUW ↦ ?_
  have k (χ : E ⟶ dual F) : resG X hUW (dualApp (χ.app V s) hW t) =
      dualApp (χ.app U (Twist.resM E (hUW.trans hW) s)) le_rfl (Twist.resM F hUW t) := by
    rw [Twist.app_resM, dualApp_res, dualApp_resM]
  rw [k, k, h U hU]

theorem frobPull_hom_ext_affine (p : ℕ) [Fact p.Prime] (h0 : (p : Γ(X, ⊤)) = 0) {φ ψ : (frobPull p h0).obj F ⟶ G}
    (h : ∀ (V : X.Opens), IsAffineOpen V → ∀ s : Γ(F, V),
      φ.app V (QCoh.pullbackSections (frob X p h0) F (le_refl V) s) =
        ψ.app V (QCoh.pullbackSections (frob X p h0) F (le_refl V) s)) : φ = ψ := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (frob X p h0)
  apply (adj.homEquiv _ _).injective
  refine hom_ext_affine fun V hV s ↦ ?_
  have k (χ : (frobPull p h0).obj F ⟶ G) : (adj.homEquiv _ _ χ).app V s =
      χ.app V (QCoh.pullbackSections (frob X p h0) F (le_refl V) s) := by
    rw [Adjunction.homEquiv_unit]
    exact congrArg (χ.app V) (QCoh.res_self _ (le_refl V) _).symm
  rw [k, k, h V hV]

end Ext

end GlobalTheory.AbDatum
end
end
