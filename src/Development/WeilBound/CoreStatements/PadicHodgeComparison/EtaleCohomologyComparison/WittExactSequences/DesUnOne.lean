import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.PfFrom
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TestOfPre

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

universe w₁

def semilinearOfAdditive {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {M : Type w} {M' : Type w₁}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (τ : M →+ M')
    (h : ∀ (a : R) x, τ (a • x) = σ a • τ x) : M →ₛₗ[σ] M' where
  toFun := τ
  map_add' := map_add τ
  map_smul' := h

def semiMor {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {C : Type u} [Category.{v} C]
    (E : C ⥤ Type v') (F : C ⥤ ModuleCat.{w} R) (F' : C ⥤ ModuleCat.{w} R') (τ : ∀ A : C, F.obj A →+ F'.obj A)
    (hσ : ∀ A (a : R) x, τ A (a • x) = σ a • τ A x)
    (hn : ∀ {A B : C} (f : A ⟶ B) x, τ B ((F.map f).hom x) = (F'.map f).hom (τ A x)) :
    CH.Mor (CH.elF E F) (CH.elF E F') σ where
  G := 𝟭 _
  τ X := semilinearOfAdditive σ (τ X.1) (hσ X.1)
  nat φ x := hn φ.1 x

theorem d_aug_zero {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {M : Type w₁} [AddCommGroup M] [Module R M] (e : ∀ T : C, M →ₗ[R] F.obj T)
    (he : ∀ {T T' : C} (φ : T ⟶ T') x, (F.map φ).hom (e T x) = e T' x) (x : M) :
    CH.d F 0 (CH.aug F e x) = 0 := by
  funext s
  simp only [CH.d, LinearMap.coe_mk, AddHom.coe_mk, CH.aug, LinearMap.pi_apply, he]
  simp

theorem ptsAug_d {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F : C ⥤ ModuleCat.{w} R) (A : C) (x : F.obj A) :
    CH.d (CH.elF (CH.pts j A) (j ⋙ F)) 0 (CH.ptsAug j F A x) = 0 :=
  d_aug_zero _ _ (fun {X Y} φ y => by
    change (F.map (j.map φ.1)).hom ((F.map X.2).hom y) = (F.map Y.2).hom y
    rw [← ModuleCat.comp_apply, ← F.map_comp]
    exact congrArg (fun g => (F.map g).hom y) φ.2) x

theorem des_semi {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F : C ⥤ ModuleCat.{w} R) (F' : C ⥤ ModuleCat.{w} R') (τ : ∀ A : C, F.obj A →+ F'.obj A)
    (hσ : ∀ A (a : R) x, τ A (a • x) = σ a • τ A x) (hb : ∀ A, Function.Bijective (τ A))
    (hn : ∀ {A B : C} (f : A ⟶ B) x, τ B ((F.map f).hom x) = (F'.map f).hom (τ A x)) (s : R) :
    DesJ j F s ↔ DesJ j F' (σ s) := by
  refine forall_congr' fun A => ?_
  let m : CH.Mor (CH.elF (CH.pts j A) (j ⋙ F)) (CH.elF (CH.pts j A) (j ⋙ F')) σ :=
    semiMor σ (CH.pts j A) (j ⋙ F) (j ⋙ F') (fun X => τ (j.obj X)) (fun X => hσ _) (fun f x => hn (j.map f) x)
  refine CrystallineSemistableComparison.P.res_semilinear m.hom (CH.ptsAug j F A) (CH.ptsAug j F' A) (semilinearOfAdditive σ (τ A) (hσ A)) s (hb A)
    (fun n => ⟨?_, ?_⟩) (fun x => ?_)
  · intro f g h
    funext t
    have h' : τ (j.obj (t.obj (Fin.last n)).1) (f t) = τ (j.obj (t.obj (Fin.last n)).1) (g t) := congrFun h t
    exact (hb _).1 h'
  · intro g
    exact ⟨fun t => Function.surjInv (hb (j.obj (t.obj (Fin.last n)).1)).2 (g t),
      funext fun t => Function.surjInv_eq (hb (j.obj (t.obj (Fin.last n)).1)).2 (g t)⟩
  · funext t
    exact hn _ x

theorem des_res {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {C : Type u} [Category.{v} C] {T : Type u'}
    [Category.{v'} T] (j : T ⥤ C) (F : C ⥤ ModuleCat.{w} R') (s : R) :
    DesJ j (F ⋙ ModuleCat.restrictScalars σ) s ↔ DesJ j F (σ s) :=
  des_semi σ j (F ⋙ ModuleCat.restrictScalars σ) F (fun A => AddMonoidHom.id (F.obj A)) (fun _ _ _ => rfl)
    (fun _ => Function.bijective_id) (fun _ _ => rfl) s

def natRes {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (σ₁ : R →+* R₁) (σ₂ : R →+* R₂)
    {C : Type u} [Category.{v} C] (F₁ : C ⥤ ModuleCat.{w} R₁) (F₂ : C ⥤ ModuleCat.{w} R₂)
    (α : ∀ A : C, F₁.obj A →+ F₂.obj A) (hα : ∀ A (a : R) x, α A (σ₁ a • x) = σ₂ a • α A x)
    (nα : ∀ {A B : C} (f : A ⟶ B) x, α B ((F₁.map f).hom x) = (F₂.map f).hom (α A x)) :
    F₁ ⋙ ModuleCat.restrictScalars σ₁ ⟶ F₂ ⋙ ModuleCat.restrictScalars σ₂ where
  app A :=
    letI : Module R (F₁.obj A) := Module.compHom _ σ₁
    letI : Module R (F₂.obj A) := Module.compHom _ σ₂
    ModuleCat.ofHom {
      toFun := α A
      map_add' := map_add (α A)
      map_smul' := hα A }
  naturality A B f := by
    ext x
    exact nα f x

theorem des_ses_nat {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    {G₁ G₂ G₃ : C ⥤ ModuleCat.{w} R} (α : G₁ ⟶ G₂) (β : G₂ ⟶ G₃)
    (hi : ∀ A, Function.Injective (α.app A).hom) (he : ∀ A, Function.Exact (α.app A).hom (β.app A).hom)
    (hs : ∀ A, Function.Surjective (β.app A).hom) (s : R) :
    (DesJ j G₁ s → DesJ j G₃ s → DesJ j G₂ (s ^ 3)) ∧ (DesJ j G₂ s → DesJ j G₃ s → DesJ j G₁ (s ^ 3)) := by
  have key : ∀ A : C,
      ((CH.cx (CH.elF (CH.pts j A) (j ⋙ G₁))).ResUpTo s (CH.ptsAug j G₁ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₃))).ResUpTo s (CH.ptsAug j G₃ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₂))).ResUpTo (s ^ 3) (CH.ptsAug j G₂ A)) ∧
      ((CH.cx (CH.elF (CH.pts j A) (j ⋙ G₂))).ResUpTo s (CH.ptsAug j G₂ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₃))).ResUpTo s (CH.ptsAug j G₃ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₁))).ResUpTo (s ^ 3) (CH.ptsAug j G₁ A)) := by
    intro A
    let a := Functor.whiskerLeft (CategoryOfElements.π (CH.pts j A)) (Functor.whiskerLeft j α)
    let b := Functor.whiskerLeft (CategoryOfElements.π (CH.pts j A)) (Functor.whiskerLeft j β)
    obtain ⟨h1, h2, h3⟩ := CrystallineSemistableComparison.P.ses_cochains a b (fun X => hi _) (fun X => he _) (fun X => hs _)
    obtain ⟨k1, k2, -⟩ := CrystallineSemistableComparison.P.res_2of3 _ _ h1 h2 h3 (α.app A).hom (β.app A).hom (hi A) (he A) (hs A)
      (CH.ptsAug j G₁ A) (CH.ptsAug j G₂ A) (CH.ptsAug j G₃ A)
      (fun x => funext fun t => (congrArg (fun φ => ModuleCat.Hom.hom φ x) (α.naturality (t.obj (Fin.last 0)).2)).symm)
      (fun x => funext fun t => (congrArg (fun φ => ModuleCat.Hom.hom φ x) (β.naturality (t.obj (Fin.last 0)).2)).symm)
      (fun x => ptsAug_d j G₂ A x) s
    exact ⟨k1, k2⟩
  exact ⟨fun h1 h3 A => (key A).1 (h1 A) (h3 A), fun h2 h3 A => (key A).2 (h2 A) (h3 A)⟩

theorem des_ses {R R₁ R₂ R₃ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₃] (σ₁ : R →+* R₁) (σ₂ : R →+* R₂) (σ₃ : R →+* R₃)
    {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F₁ : C ⥤ ModuleCat.{w} R₁) (F₂ : C ⥤ ModuleCat.{w} R₂) (F₃ : C ⥤ ModuleCat.{w} R₃)
    (α : ∀ A : C, F₁.obj A →+ F₂.obj A) (β : ∀ A : C, F₂.obj A →+ F₃.obj A)
    (hα : ∀ A (a : R) x, α A (σ₁ a • x) = σ₂ a • α A x) (hβ : ∀ A (a : R) x, β A (σ₂ a • x) = σ₃ a • β A x)
    (nα : ∀ {A B : C} (f : A ⟶ B) x, α B ((F₁.map f).hom x) = (F₂.map f).hom (α A x))
    (nβ : ∀ {A B : C} (f : A ⟶ B) x, β B ((F₂.map f).hom x) = (F₃.map f).hom (β A x))
    (hi : ∀ A, Function.Injective (α A)) (he : ∀ A, Function.Exact (α A) (β A)) (hs : ∀ A, Function.Surjective (β A)) (s : R) :
    (DesJ j F₁ (σ₁ s) → DesJ j F₃ (σ₃ s) → DesJ j F₂ (σ₂ (s ^ 3))) ∧
    (DesJ j F₂ (σ₂ s) → DesJ j F₃ (σ₃ s) → DesJ j F₁ (σ₁ (s ^ 3))) := by
  have key := des_ses_nat j (natRes σ₁ σ₂ F₁ F₂ α hα nα) (natRes σ₂ σ₃ F₂ F₃ β hβ nβ)
    (fun A x y h => hi A h) (fun A y => he A y) (fun A y => hs A y) s
  refine ⟨fun h1 h3 => ?_, fun h2 h3 => ?_⟩
  · exact (des_res σ₂ j F₂ (s ^ 3)).1 (key.1 ((des_res σ₁ j F₁ s).2 h1) ((des_res σ₃ j F₃ s).2 h3))
  · exact (des_res σ₁ j F₁ (s ^ 3)).1 (key.2 ((des_res σ₂ j F₂ s).2 h2) ((des_res σ₃ j F₃ s).2 h3))

end CrystallineSemistableComparison.D
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

section Span
universe w₁
variable {R : Type} [CommRing R]

theorem res_add {K : Cx.{w} R} {M : Type w₁} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} {a b : R}
    (ha : K.ResUpTo a ε) (hb : K.ResUpTo b ε) : K.ResUpTo (a + b) ε := by
  refine ⟨ha.1, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · rw [add_smul, ha.2.1 x hx, hb.2.1 x hx, add_zero]
  · obtain ⟨x, hx⟩ := ha.2.2.1 y hy
    obtain ⟨x', hx'⟩ := hb.2.2.1 y hy
    exact ⟨x + x', by rw [map_add, hx, hx', add_smul]⟩
  · obtain ⟨x, hx⟩ := ha.2.2.2 n y hy
    obtain ⟨x', hx'⟩ := hb.2.2.2 n y hy
    exact ⟨x + x', by rw [map_add, hx, hx', add_smul]⟩

theorem res_mul {K : Cx.{w} R} {M : Type w₁} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} (r : R) {a : R}
    (ha : K.ResUpTo a ε) : K.ResUpTo (r * a) ε := by
  refine ⟨ha.1, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · rw [mul_smul, ha.2.1 x hx, smul_zero]
  · obtain ⟨x, hx⟩ := ha.2.2.1 y hy
    exact ⟨r • x, by rw [map_smul, hx, mul_smul]⟩
  · obtain ⟨x, hx⟩ := ha.2.2.2 n y hy
    exact ⟨r • x, by rw [map_smul, hx, mul_smul]⟩

theorem res_kill {K : Cx.{w} R} {M : Type w₁} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} (a : R)
    (h0 : ∀ x, K.d 0 (ε x) = 0) (hM : ∀ x : M, a • x = 0) (hK : ∀ n (y : K.X n), a • y = 0) : K.ResUpTo a ε :=
  ⟨h0, fun x _ => hM x, fun y _ => ⟨0, by rw [map_zero, hK]⟩, fun n y _ => ⟨0, by rw [map_zero, hK]⟩⟩

theorem d_ptsAug {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F : C ⥤ ModuleCat.{w} R) (A : C) (x : F.obj A) : d (elF (pts j A) (j ⋙ F)) 0 (ptsAug j F A x) = 0 := by
  funext s
  have key : ∀ i : Fin 2, ((elF (pts j A) (j ⋙ F)).map (GlobalTheory.CatH.toLast i s)).hom (ptsAug j F A x (GlobalTheory.CatH.face i s)) =
      (F.map (s.obj (Fin.last 1)).2).hom x := by
    intro i
    change (F.map ((GlobalTheory.CatH.face i s).obj (Fin.last 0)).2 ≫ F.map (j.map (GlobalTheory.CatH.toLast i s).1)).hom x = _
    rw [← F.map_comp]
    congr 3
    exact (GlobalTheory.CatH.toLast i s).2
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ((elF (pts j A) (j ⋙ F)).map (GlobalTheory.CatH.toLast i s)).hom
    (ptsAug j F A x (GlobalTheory.CatH.face i s)) = 0
  rw [Fin.sum_univ_two, key, key]
  simp

end Span

def ptsG {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    {C' : Type u''} [Category.{v} C'] (G : C ⥤ C') (A : C) : pts j A ⟶ pts (j ⋙ G) (G.obj A) where
  app t := TypeCat.ofHom fun y => G.map y
  naturality t t' φ := by
    ext y
    exact G.map_comp y (j.map φ)

theorem des_ff {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    {C' : Type u''} [Category.{v} C'] (G : C ⥤ C') [G.Full] [G.Faithful] (F : C' ⥤ ModuleCat.{w} R) (s : R) :
    DesJ (j ⋙ G) F s → DesJ j (G ⋙ F) s := by
  intro h A
  have hb : ∀ t, Function.Bijective ((ptsG j G A).app t) := fun t =>
    ⟨fun y y' (e : G.map y = G.map y') => G.map_injective e, fun y => ⟨G.preimage y, G.map_preimage y⟩⟩
  have := (CrystallineSemistableComparison.P.res_semilinear (elMor (ptsG j G A) ((j ⋙ G) ⋙ F)).hom (ptsAug (j ⋙ G) F (G.obj A))
    (ptsAug j (G ⋙ F) A) LinearMap.id s Function.bijective_id (CrystallineSemistableComparison.P.el_iso _ _ hb) (fun x => rfl)).1 (h (G.obj A))
  exact this

theorem des_span {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C) (F : C ⥤ ModuleCat.{w} R) (S : Set R)
    (h : ∀ a ∈ S, DesJ j F a ∨ ∀ (A : C) (x : F.obj A), a • x = 0) : ∀ s ∈ Ideal.span S, DesJ j F s := by
  have kill : ∀ a : R, (∀ (A : C) (x : F.obj A), a • x = 0) → DesJ j F a := fun a ha A =>
    res_kill a (d_ptsAug j F A) (ha A) fun n y => by funext s; exact ha _ (y s)
  intro s hs
  induction hs using Submodule.span_induction with
  | mem a ha => exact (h a ha).elim id (kill a)
  | zero => exact kill 0 fun _ x => zero_smul R x
  | add a b _ _ ha hb => exact fun A => res_add (ha A) (hb A)
  | smul r a _ ha => exact fun A => res_mul r (ha A)

end CrystallineSemistableComparison.D
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe v' u'

namespace CrystallineSemistableComparison.D

section Abs

variable {R : Type} [CommRing R] {p : ℕ}

theorem pf_ext {X Y : PfC p R} {f g : X ⟶ Y} (h : ∀ x, f.hom.hom x = g.hom.hom x) : f = g :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext h))

theorem injUpTo_span {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (S : Set R)
    (f : M →ₗ[R] N) (h : ∀ s ∈ S, InjUpTo s f) : ∀ s ∈ Ideal.span S, InjUpTo s f := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => intro z _; exact zero_smul R z
  | add x y _ _ hx hy => intro z hz; rw [add_smul, hx z hz, hy z hz, add_zero]
  | smul a x _ hx => intro z hz; rw [smul_eq_mul, mul_smul, hx z hz, smul_zero]

theorem exactUpTo_span {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N]
    [Module R P] (S : Set R) (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : ∀ s ∈ S, ExactUpTo s f g) :
    ∀ s ∈ Ideal.span S, ExactUpTo s f g := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => intro z _; exact ⟨0, by rw [map_zero, zero_smul]⟩
  | add x y _ _ hx hy =>
    intro z hz
    obtain ⟨u, hu⟩ := hx z hz
    obtain ⟨v, hv⟩ := hy z hz
    exact ⟨u + v, by rw [map_add, hu, hv, add_smul]⟩
  | smul a x _ hx =>
    intro z hz
    obtain ⟨u, hu⟩ := hx z hz
    exact ⟨a • u, by rw [map_smul, hu, smul_eq_mul, mul_smul]⟩

variable {T : Type u'} [Category.{v'} T] (j : T ⥤ PfC p R)
variable (A : PfC p R) (B : Type) [CommRing B] [Algebra R B] [Algebra A.obj B] [IsScalarTower R A.obj B] (hB : Pf p B)
  (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra R (K n)] [∀ n, Algebra A.obj (K n)] [∀ n, IsScalarTower R A.obj (K n)]
  (hK : ∀ n, Pf p (K n)) (ι : ∀ n, Fin n → (B →ₐ[A.obj] K n)) (hι : ∀ n, IsWP (ι n))
  (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A.obj] K (n + 1)))
  (hδ : ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i))
  (hrel : ∀ (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1)),
    (δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k)) = (δ (n + 1) k).comp (δ n i))
  (h0 : Function.Bijective (algebraMap A.obj (K 0))) (h1 : Function.Bijective (ι 1 0))

def univMap (n : ℕ) (X : PfC p R) (x : A ⟶ X) (y : Fin n → (pfOb (R := R) B hB ⟶ X))
    (hxy : ∀ i, pfFrom A B hB ≫ y i = x) : pfOb (R := R) (K n) (hK n) ⟶ X :=
  ObjectProperty.homMk (CommAlgCat.ofHom
    { toRingHom := Classical.choose ((hι n).ex X.obj x.hom.hom.toRingHom (fun i => (y i).hom.hom.toRingHom)
        (fun i => RingHom.ext fun c => congrArg (fun φ => φ.hom.hom c) (hxy i)))
      commutes' := fun c => by
        have h := (Classical.choose_spec ((hι n).ex X.obj x.hom.hom.toRingHom (fun i => (y i).hom.hom.toRingHom)
          (fun i => RingHom.ext fun c => congrArg (fun φ => φ.hom.hom c) (hxy i)))).1
        rw [IsScalarTower.algebraMap_apply R A.obj (K n)]
        exact (RingHom.congr_fun h _).trans (x.hom.hom.commutes c) })

theorem univMap_spec (n : ℕ) (X : PfC p R) (x : A ⟶ X) (y : Fin n → (pfOb (R := R) B hB ⟶ X))
    (hxy : ∀ i, pfFrom A B hB ≫ y i = x) :
    (univMap A B hB K hK ι hι n X x y hxy).hom.hom.toRingHom.comp (algebraMap A.obj (K n)) = x.hom.hom.toRingHom ∧
      ∀ i, (univMap A B hB K hK ι hι n X x y hxy).hom.hom.toRingHom.comp (ι n i : B →+* K n) = (y i).hom.hom.toRingHom :=
  Classical.choose_spec ((hι n).ex X.obj x.hom.hom.toRingHom (fun i => (y i).hom.hom.toRingHom)
    (fun i => RingHom.ext fun c => congrArg (fun φ => φ.hom.hom c) (hxy i)))

def mkPowers : Powers j A where
  B := pfOb (R := R) B hB
  f := pfFrom A B hB
  K n := pfOb (R := R) (K n) (hK n)
  a n := pfFrom A (K n) (hK n)
  ι n i := pfHom ((ι n i).restrictScalars R)
  w n i := pf_ext fun c => (ι n i).commutes c
  δ n k := pfHom ((δ n k).restrictScalars R)
  aδ n k := pf_ext fun c => (δ n k).commutes c
  ιδ n k i := pf_ext fun c => AlgHom.congr_fun (hδ n k i) c
  rel n k i := pf_ext fun c => AlgHom.congr_fun (hrel n k i) c
  iso0 := by
    rw [← ObjectProperty.isIso_hom_iff]
    exact (CommAlgCat.isoMk (AlgEquiv.ofBijective (IsScalarTower.toAlgHom R A.obj (K 0)) h0)).isIso_hom
  iso1 := by
    rw [← ObjectProperty.isIso_hom_iff]
    exact (CommAlgCat.isoMk (AlgEquiv.ofBijective ((ι 1 0).restrictScalars R) h1)).isIso_hom
  univ n t x y hxy := by
    refine ⟨univMap A B hB K hK ι hι n (j.obj t) x y hxy, ⟨?_, fun i => ?_⟩, fun z hz => ?_⟩
    · exact pf_ext fun c => RingHom.congr_fun (univMap_spec A B hB K hK ι hι n (j.obj t) x y hxy).1 c
    · exact pf_ext fun c => RingHom.congr_fun ((univMap_spec A B hB K hK ι hι n (j.obj t) x y hxy).2 i) c
    · have hs := univMap_spec A B hB K hK ι hι n (j.obj t) x y hxy
      exact pf_ext fun c => RingHom.congr_fun ((hι n).uniq (j.obj t).obj z.hom.hom.toRingHom
        (univMap A B hB K hK ι hι n (j.obj t) x y hxy).hom.hom.toRingHom
        (RingHom.ext fun c => (congrArg (fun φ => φ.hom.hom c) hz.1).trans (RingHom.congr_fun hs.1 c).symm)
        (fun i => RingHom.ext fun c => (congrArg (fun φ => φ.hom.hom c) (hz.2 i)).trans
          (RingHom.congr_fun (hs.2 i) c).symm)) c

theorem mkPowers_dK (N : Type) [AddCommGroup N] [Module R N] (n : ℕ) (w : N ⊗[R] K n) :
    (mkPowers j A B hB K hK ι hι δ hδ hrel h0 h1).dK j (tensF p R N) n w = ((alt (δ n)).restrictScalars R).lTensor N w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv]
  | tmul a b =>
    rw [Powers.dK, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, alt, LinearMap.sum_apply,
      LinearMap.sum_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    exact (map_zsmul (TensorProduct.mk R N (K (n + 1)) a) _ _).symm

end Abs

theorem powers_abs {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] (p : ℕ) [Fact p.Prime]
    {T : Type u'} [Category.{v'} T] (j : T ⥤ PfC p R)
    (r : ℕ → R) (hr : IsRt p r) (hdiv : ∀ a : R, a ≠ 0 → ∃ M : ℕ, a ∣ r 0 ^ M)
    (N : Type) [AddCommGroup N] [Module R N]
    (A : PfC p R) (B : Type) [CommRing B] [Algebra R B] [Algebra A.obj B] [IsScalarTower R A.obj B] (hB : Pf p B)
    (hC : Cov p (fun k => algebraMap R A.obj (r k)) B)
    (H1 : ∀ (t : T) (x : A ⟶ j.obj t), ∃ y : pfOb (R := R) B hB ⟶ j.obj t, pfFrom A B hB ≫ y = x)
    (H3 : ∃ (t₀ : T) (g : pfOb (R := R) B hB ⟶ j.obj t₀),
      (∀ (t : T) (y : pfOb (R := R) B hB ⟶ j.obj t), ∃! φ : t₀ ⟶ t, g ≫ j.map φ = y) ∧
      Almost (Ideal.span (Set.range r)) ((tensF p R N).map g).hom) :
    ∃ P : Powers j A, P.Good j (tensF p R N) (Ideal.span (Set.range r)) := by
  choose K iK aK ι hι using fun n => Leaf.wp_ex A.obj B n
  let _ : ∀ n, Algebra R (K n) := fun n => ((algebraMap A.obj (K n)).comp (algebraMap R A.obj)).toAlgebra
  have _ : ∀ n, IsScalarTower R A.obj (K n) := fun n => IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨h0, h1, δ, hδ⟩ := Leaf.wp_cof A.obj B K ι hι
  have hrel := Leaf.wp_rel A.obj B K ι δ hι hδ
  have hK : ∀ n, Pf p (K n) := fun n => Leaf.wp_pf p A.obj B (K n) n (ι n) (hι n) A.property hB
  obtain ⟨hc1, hc2⟩ := Leaf.cech_tens p R r N A.obj B K ι δ hr hdiv A.property hB hC hι hδ
  refine ⟨mkPowers j A B hB K hK ι hι δ hδ hrel h0 h1, H1, fun s hs => ⟨?_, fun n => ?_⟩, H3⟩
  · refine injUpTo_span _ _ (fun s' hs' => ?_) s hs
    obtain ⟨k, rfl⟩ := hs'
    intro w hw
    rw [mkPowers_dK] at hw
    exact hc1 w hw k
  · refine exactUpTo_span _ _ _ (fun s' hs' => ?_) s hs
    obtain ⟨k, rfl⟩ := hs'
    intro w hw
    rw [mkPowers_dK] at hw
    obtain ⟨x, hx⟩ := hc2 n w hw k
    exact ⟨x, (mkPowers_dK j A B hB K hK ι hι δ hδ hrel h0 h1 N n x).trans hx⟩

end CrystallineSemistableComparison.D
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem split_clause (A : PfC l (Ob l)) (B : Type) [CommRing B] [Algebra (Ob l) B] [Algebra A.obj B]
    [IsScalarTower (Ob l) A.obj B] (hB : Pf l B) (hS : Splits l (algebraMap (Ob l) A.obj (rt l 0)) (algebraMap A.obj B)) :
    ∀ (t : Test l) (x : A ⟶ (testι l ⋙ toPf l).obj t), ∃ y : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t, pfFrom A B hB ≫ y = x := by
  intro t x
  let xa : A.obj →ₐ[Ob l] t.obj.A := x.hom.hom
  have hPf : Pf l t.obj.A := ⟨t.obj.natCast_l, t.obj.perf.bijective_frobenius⟩
  have hV : VAL ((xa : A.obj →+* t.obj.A) (algebraMap (Ob l) A.obj (rt l 0))) := by
    have e : (xa : A.obj →+* t.obj.A) (algebraMap (Ob l) A.obj (rt l 0)) = t.obj.pi := by
      change xa (algebraMap (Ob l) A.obj (rt l 0)) = t.obj.s (pFlat l)
      rw [xa.commutes, ← (isRt_rt l).2]; rfl
    rw [e]; exact t.property.2
  obtain ⟨y, hy⟩ := hS t.obj.A (xa : A.obj →+* t.obj.A) hPf t.property.1 hV
  let ya : B →ₐ[Ob l] t.obj.A :=
    { y with
      commutes' := fun c => by
        change y (algebraMap (Ob l) B c) = algebraMap (Ob l) t.obj.A c
        rw [IsScalarTower.algebraMap_apply (Ob l) A.obj B c, ← RingHom.comp_apply, hy]
        exact xa.commutes c }
  refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom ya), ?_⟩
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  change y (algebraMap A.obj B a) = xa a
  exact RingHom.congr_fun hy a

theorem test_clause (N : Type) [AddCommGroup N] [Module (Ob l) N] (M : ℕ) (hN : ∀ x : N, pFlat l ^ M • x = 0)
    (B : Type) [CommRing B] [Algebra (Ob l) B] (hB : Pf l B) (hA : AIC B) (hV : VAL (algebraMap (Ob l) B (rt l 0))) :
    ∃ (t₀ : Test l) (g : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t₀),
      (∀ (t : Test l) (y : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t), ∃! φ : t₀ ⟶ t, g ≫ (testι l ⋙ toPf l).map φ = y) ∧
      Almost (Ideal.span (Set.range (rt l))) ((tensF l (Ob l) N).map g).hom := by
  have hr := isRt_rt l
  have hIsRt : IsRt l (fun k => algebraMap (Ob l) B (rt l k)) := fun k => by
    simp only; rw [← map_pow, hr.1 k]
  obtain ⟨T, _, g, hPf, hAIC, hVAL, hcompl, hnzd, hsurj, hinj, huniv⟩ :=
    Leaf.test_of_pre l B (fun k => algebraMap (Ob l) B (rt l k)) hB hIsRt hA hV
  let s : Ob l →+* T := g.comp (algebraMap (Ob l) B)
  have hs0 : s (pFlat l) = g (algebraMap (Ob l) B (rt l 0)) := by
    simp only [s, RingHom.comp_apply, hr.2]
  letI : Algebra (Ob l) T := s.toAlgebra
  let P0 : PAlg l :=
    { A := T, s := s, perf := ⟨hPf.bij⟩
      compl := by rw [hs0]; exact hcompl
      tf := by rw [hs0]; exact hnzd }
  let t₀ : Test l := ⟨P0, hAIC, by show VAL (s (pFlat l)); rw [hs0]; exact hVAL⟩
  let gA : B →ₐ[Ob l] T := { g with commutes' := fun _ => rfl }
  let g' : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t₀ := ObjectProperty.homMk (CommAlgCat.ofHom gA)
  refine ⟨t₀, g', ?_, ?_⟩
  · intro t y
    let ya : B →ₐ[Ob l] t.obj.A := y.hom.hom
    have hc : (ya : B →+* t.obj.A) (algebraMap (Ob l) B (rt l 0)) = t.obj.s (pFlat l) := by
      change ya (algebraMap (Ob l) B (rt l 0)) = _
      rw [ya.commutes, hr.2]; rfl
    obtain ⟨ψ, hψ, huq⟩ := huniv t.obj.A (ya : B →+* t.obj.A) (by rw [hc]; exact t.obj.compl) (by rw [hc]; exact t.obj.tf)
    have hcomm : ψ.comp P0.s = t.obj.s := by
      ext c
      change ψ (g (algebraMap (Ob l) B c)) = t.obj.s c
      rw [← RingHom.comp_apply ψ g, hψ]
      exact ya.commutes c
    refine ⟨ObjectProperty.homMk (⟨ψ, hcomm⟩ : PAlg.Hom P0 t.obj), ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro b
      change ψ (g b) = ya b
      exact RingHom.congr_fun hψ b
    · intro φ hφ
      apply ObjectProperty.hom_ext
      apply PAlg.Hom.ext
      apply huq
      ext b
      have := congrArg (fun u => u.hom.hom b) hφ
      exact this
  · have key : ((tensF l (Ob l) N).map g').hom = gA.toLinearMap.lTensor N := rfl
    obtain ⟨hsT, hkT⟩ := Leaf.tens_compl (Ob l) (rt l) M N B T gA (by rw [hr.2]; exact hN)
      (fun y => hsurj M y) (fun x hx k => by rw [Algebra.smul_def]; exact hinj M x hx k)
    rw [key]
    intro a ha
    refine ⟨?_, fun y => ?_⟩
    · induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        intro w hw; exact hkT w hw k
      | zero => intro w _; exact zero_smul _ _
      | add x y _ _ hx hy => intro w hw; rw [add_smul, hx w hw, hy w hw, add_zero]
      | smul c x _ hx => intro w hw; rw [smul_eq_mul, mul_smul, hx w hw, smul_zero]
    · exact hsT (a • y)

end CrystallineSemistableComparison.D
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem powers_good (h : ObFacts l) (N : Type) [AddCommGroup N] [Module (Ob l) N] (M : ℕ) (hN : ∀ x : N, pFlat l ^ M • x = 0)
    (A : PfC l (Ob l)) : ∃ P : Powers (testι l ⋙ toPf l) A,
      P.Good (testι l ⋙ toPf l) (tensF l (Ob l) N) (Ideal.span (Set.range (rt l))) := by
  obtain ⟨_, _, hdiv, -⟩ := h
  obtain ⟨hr, hr0⟩ := isRt_rt l
  have hrA : IsRt l (fun k => algebraMap (Ob l) A.obj (rt l k)) := fun k => by
    simp only [← map_pow, hr k]
  obtain ⟨B, _, _, hB, hC, hAIC, hVAL, hS⟩ := Leaf.cov_tower l A.obj _ A.property hrA
  let _ : Algebra (Ob l) B := ((algebraMap A.obj B).comp (algebraMap (Ob l) A.obj)).toAlgebra
  have _ : IsScalarTower (Ob l) A.obj B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact powers_abs l (testι l ⋙ toPf l) (rt l) hr
    (fun a ha => by obtain ⟨M, hM⟩ := hdiv a ha; exact ⟨M, hr0 ▸ hM⟩) N A B hB hC
    (split_clause l A B hB hS) (test_clause l N M hN B hB hAIC hVAL)

end CrystallineSemistableComparison.D
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem rt_pow (k N : ℕ) : rt l (k + N) ^ (l ^ N) = rt l k := by
  induction N with
  | zero => rw [pow_zero, pow_one, add_zero]
  | succ N ih => rw [pow_succ', pow_mul, ← add_assoc, (isRt_rt l).1 (k + N), ih]

theorem rt_ideal (N : ℕ) : Ideal.span (Set.range (rt l)) ≤
    Ideal.span ((fun a => a ^ N) '' (Ideal.span (Set.range (rt l)) : Set (Ob l))) := by
  rw [Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  have hN : N ≤ l ^ N := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  rw [← rt_pow l k N, ← Nat.sub_add_cancel hN, pow_add]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨rt l (k + N), Ideal.subset_span ⟨k + N, rfl⟩, rfl⟩)

theorem des_tens (h : ObFacts l) (N : Type) [AddCommGroup N] [Module (Ob l) N] (M : ℕ) (hN : ∀ x : N, pFlat l ^ M • x = 0) (k : ℕ) :
    Des (toPf l ⋙ tensF l (Ob l) N) (rt l k) := by
  have := (toPf_full l).1
  have := (toPf_full l).2
  have hdes : DesJ (testι l ⋙ toPf l) (tensF l (Ob l) N) (rt l k) := fun A =>
    CrystallineSemistableComparison.P.induct (testι l ⋙ toPf l) (tensF l (Ob l) N) _ (rt_ideal l) (fun A => powers_good l h N M hN A) A _
      (Ideal.subset_span ⟨k, rfl⟩)
  exact des_ff (testι l) (toPf l) _ _ hdes

end CrystallineSemistableComparison.D
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.D

section SlopeTestRemainingChoices

variable {U : Type} [CommRing U]

def mulQ (a : U) (n : ℕ) : U ⧸ Ideal.span {a ^ 1} →ₗ[U] U ⧸ Ideal.span {a ^ (n + 1)} :=
  Submodule.liftQ _ ((Ideal.span {a ^ (n + 1)}).mkQ ∘ₗ LinearMap.mulLeft U (a ^ n)) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    change Ideal.Quotient.mk _ (a ^ n * a ^ 1) = 0
    rw [pow_one, ← pow_succ]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))

theorem mulQ_mk (a : U) (n : ℕ) (x : U) :
    mulQ a n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (a ^ n * x) := rfl

theorem mulQ_inj (a : U) (ha : a ∈ nonZeroDivisors U) (n : ℕ) : Function.Injective (mulQ a n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mulQ_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, hc⟩ := hx
  refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨c, ?_⟩)
  have hn := pow_mem ha n
  rw [pow_succ, mul_comm (a ^ n) a, ← mul_assoc, mul_comm _ (a ^ n)] at hc
  rw [pow_one]
  exact (mul_cancel_left_mem_nonZeroDivisors hn).1 hc

theorem mulQ_exact (a : U) (n : ℕ) :
    Function.Exact (mulQ a n) (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow a n.le_succ))) := by
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Ideal.Quotient.mk _ c, by rw [mulQ_mk, mul_comm]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [mulQ_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hz
    obtain ⟨d, hd⟩ := hz
    exact ⟨c - d * a, by rw [sub_mul, mul_assoc, ← pow_succ', hd]; ring⟩

end SlopeTestRemainingChoices

end CrystallineSemistableComparison.D
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.D

open PAlg

variable {l : ℕ} [Fact l.Prime]

theorem flagDomainConj_hostXi_eq_neg : WittVector.constantCoeff (xi0 l) = -pFlat l := by
  rw [xi0, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
  exact congrArg Neg.neg (WittVector.teichmuller_coeff_zero l _)

theorem un_rep {A : PAlg l} {n : ℕ} (x : A.Un n) : ∃ w : A.W, x = Ideal.Quotient.mk _ (A.th w) := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {A.xi}) u
  exact ⟨w, rfl⟩

variable (A : PAlg l)

def rho0 : A.U →+* A.A ⧸ Ideal.span {A.pi} :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp WittVector.constantCoeff) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have e : WittVector.constantCoeff A.xi = -A.pi := by
      change (WittVector.map A.s (xi0 l)).coeff 0 = -A.s (pFlat l)
      rw [WittVector.map_coeff, ← map_neg, ← flagDomainConj_hostXi_eq_neg]; rfl
    rw [RingHom.comp_apply, map_mul, e]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_span_singleton_self _)))

def rho : A.Un 1 →+* A.A ⧸ Ideal.span {A.pi} :=
  Ideal.Quotient.lift _ (rho0 A) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast, ← map_natCast (Ideal.Quotient.mk (Ideal.span {A.pi})), A.natCast_l, map_zero,
      zero_pow one_ne_zero, mul_zero]

theorem rho_mk (w : A.W) : rho A (Ideal.Quotient.mk _ (A.th w)) = Ideal.Quotient.mk _ (w.coeff 0) := rfl

theorem rho_bij (hU : RU l) : Function.Bijective (rho A) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨w, rfl⟩ := un_rep x
    rw [rho_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    have := ((hU A).2 w).2 hx
    exact Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [pow_one])
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ (A.th (WittVector.teichmuller l a)), by rw [rho_mk, WittVector.teichmuller_coeff_zero]⟩

theorem span_pi_eq : (Ideal.span {A.pi}).restrictScalars (Ob l) = (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, trivial, by rw [Algebra.smul_def, mul_comm]; rfl⟩
  · rintro ⟨b, _, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, mul_comm]; rfl⟩

def kappa : (A.A ⧸ Ideal.span {A.pi}) ≃ₗ[Ob l] A.A ⧸ (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A) :=
  (Submodule.Quotient.restrictScalarsEquiv (Ob l) (Ideal.span {A.pi})).symm.trans (Submodule.quotEquivOfEq _ _ (span_pi_eq A))

def tau1 : A.Un 1 →+ (Ob l ⧸ Ideal.span {pFlat l}) ⊗[Ob l] A.A :=
  ((TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm.toAddMonoidHom.comp
    (kappa A).toAddMonoidHom).comp (rho A).toAddMonoidHom

theorem kappa_mk (x : A.A) :
    kappa A (Ideal.Quotient.mk _ x) = Submodule.Quotient.mk (p := (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A)) x := by
  rfl

theorem tau1_mk (w : A.W) : tau1 A (Ideal.Quotient.mk _ (A.th w)) = (1 : Ob l ⧸ Ideal.span {pFlat l}) ⊗ₜ[Ob l] w.coeff 0 := by
  change (TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm (kappa A (rho A (Ideal.Quotient.mk _ (A.th w)))) = _
  rw [rho_mk, kappa_mk]
  exact TensorProduct.quotTensorEquivQuotSMul_symm_mk _ _

theorem tau1_bijective (hU : RU l) : Function.Bijective (tau1 A) :=
  (TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm.bijective.comp
    ((kappa A).bijective.comp (rho_bij A hU))

theorem tau1_smul (a : Ainf l) (x : A.Un 1) :
    tau1 A (a • x) = WittVector.constantCoeff a • tau1 A x := by
  obtain ⟨w, rfl⟩ := un_rep x
  have e : a • (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (A.th w)) =
      Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (A.th (A.sW a * w)) := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (Ainf l) A.U, Ideal.Quotient.algebraMap_eq, ← map_mul, map_mul A.th]; rfl
  rw [e, tau1_mk, tau1_mk, ← TensorProduct.tmul_smul, WittVector.mul_coeff_zero, Algebra.smul_def]
  change _ ⊗ₜ[Ob l] ((WittVector.map A.s a).coeff 0 * _) = _
  rw [WittVector.map_coeff]; rfl

end CrystallineSemistableComparison.D
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem rtW_dvd (k : ℕ) : rtW l (k + 2) ^ 3 ∣ rtW l k ∧ (rtW l k).coeff 0 = rt l k := by
  refine ⟨?_, WittVector.teichmuller_coeff_zero l _⟩
  have h := (isRt_rt l).1
  have e : rt l k = rt l (k + 2) ^ (l * l) := by rw [pow_mul, h (k + 1), h k]
  have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl : 3 ≤ l * l := by nlinarith
  refine ⟨WittVector.teichmuller l (rt l (k + 2) ^ (l * l - 3)), ?_⟩
  rw [rtW, rtW, e, ← map_pow, ← map_mul, ← pow_add, Nat.add_sub_cancel' hl]

theorem des_Un_one (h : ObFacts l) (hU : RU l) (k : ℕ) : Des (UnF l 1) (rtW l k) := by
  have hd := des_tens l h (Ob l ⧸ Ideal.span {pFlat l}) 1 (fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (pFlat l ^ 1 * y) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (by rw [pow_one]; exact Ideal.mem_span_singleton_self _))) k
  have hn : ∀ {A B : PAlg l} (f : A ⟶ B) (x : (UnF l 1).obj A),
      tau1 B (((UnF l 1).map f).hom x) = ((toPf l ⋙ tensF l (Ob l) (Ob l ⧸ Ideal.span {pFlat l})).map f).hom (tau1 A x) := by
    intro A B f x
    obtain ⟨w, rfl⟩ := un_rep x
    have e : ((UnF l 1).map f).hom (Ideal.Quotient.mk _ (A.th w)) = Ideal.Quotient.mk _ (B.th (PAlg.mapW f w)) := rfl
    rw [e, tau1_mk, tau1_mk, PAlg.mapW, WittVector.map_coeff]
    rfl
  refine (des_semi WittVector.constantCoeff (testι l) (UnF l 1) (toPf l ⋙ tensF l (Ob l) (Ob l ⧸ Ideal.span {pFlat l}))
    (fun A => tau1 A) (fun A a x => tau1_smul A a x) (fun A => tau1_bijective A hU) hn (rtW l k)).2 ?_
  change DesJ _ _ ((rtW l k).coeff 0)
  rw [(rtW_dvd l k).2]
  exact hd

theorem des_Un (h : ObFacts l) (hU : RU l) (n k : ℕ) : Des (UnF l n) (rtW l k) := by
  induction n generalizing k with
  | zero =>
    refine des_span (testι l) (UnF l 0) {rtW l k} (fun a _ => Or.inr fun A x => ?_) _ (Ideal.subset_span rfl)
    have hz : ∀ z : A.Un 0, z = 0 := fun z => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact Ideal.Quotient.eq_zero_iff_mem.2 (by rw [pow_zero, Ideal.span_singleton_one]; trivial)
    exact hz _
  | succ n ih =>
    have hα : ∀ (A : PAlg l) (a : Ainf l) (x : (UnF l 1).obj A),
        (mulQ (l : A.U) n).toAddMonoidHom (RingHom.id (Ainf l) a • x) = RingHom.id (Ainf l) a • (mulQ (l : A.U) n).toAddMonoidHom x := by
      intro A a x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      change mulQ (l : A.U) n (a • Ideal.Quotient.mk _ u) = a • mulQ (l : A.U) n (Ideal.Quotient.mk _ u)
      rw [algebra_compatible_smul A.U a, LinearMap.map_smul, ← algebra_compatible_smul]
    have hβ : ∀ (A : PAlg l) (a : Ainf l) (x : (UnF l (n + 1)).obj A),
        (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom
          (RingHom.id (Ainf l) a • x) = RingHom.id (Ainf l) a •
        (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom x := by
      intro A a x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    have nα : ∀ {A B : PAlg l} (f : A ⟶ B) (x : (UnF l 1).obj A),
        (mulQ (l : B.U) n).toAddMonoidHom (((UnF l 1).map f).hom x) = ((UnF l (n + 1)).map f).hom ((mulQ (l : A.U) n).toAddMonoidHom x) := by
      intro A B f x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk _ ((l : B.U) ^ n * PAlg.mapU f u) = Ideal.Quotient.mk _ (PAlg.mapU f ((l : A.U) ^ n * u))
      rw [map_mul (PAlg.mapU f), map_pow (PAlg.mapU f), map_natCast (PAlg.mapU f)]
    have nβ : ∀ {A B : PAlg l} (f : A ⟶ B) (x : (UnF l (n + 1)).obj A),
        (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : B.U) n.le_succ))).toAddMonoidHom
          (((UnF l (n + 1)).map f).hom x) = ((UnF l n).map f).hom
        ((Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom x) := by
      intro A B f x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    have key := (des_ses (RingHom.id (Ainf l)) (RingHom.id _) (RingHom.id _) (testι l) (UnF l 1) (UnF l (n + 1)) (UnF l n)
      (fun A => (mulQ (l : A.U) n).toAddMonoidHom)
      (fun A => (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom)
      hα hβ nα nβ (fun A => mulQ_inj _ (hU A).1 n) (fun A => mulQ_exact _ n)
      (fun A y => by
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨Ideal.Quotient.mk _ z, rfl⟩) (rtW l (k + 2))).1
      (des_Un_one l h hU (k + 2)) (ih (k + 2))
    exact des_span (testι l) (UnF l (n + 1)) {rtW l (k + 2) ^ 3}
      (fun a ha => Or.inl (by rw [Set.mem_singleton_iff.1 ha]; exact key)) _ (Ideal.mem_span_singleton.2 (rtW_dvd l k).1)

theorem wm_span (h : ObFacts l) (s : Ainf l) (hs : InWm l s) (n : ℕ) :
    s ∈ Ideal.span (insert ((l : Ainf l) ^ n) (Set.range (rtW l))) := by
  obtain ⟨_, _, _, h4⟩ := h
  have hr : ∀ k, rtW l k ∈ Ideal.span (insert ((l : Ainf l) ^ n) (Set.range (rtW l))) :=
    fun k => Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
  have hl : (l : Ainf l) ^ n ∈ Ideal.span (insert ((l : Ainf l) ^ n) (Set.range (rtW l))) :=
    Ideal.subset_span (Set.mem_insert _ _)
  cases n with
  | zero =>
    rw [Ideal.eq_top_of_isUnit_mem _ hl (by rw [pow_zero]; exact isUnit_one)]
    exact Submodule.mem_top
  | succ m =>
    obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff s m
    rw [sub_eq_iff_eq_add] at hc
    rw [hc]
    refine add_mem (Ideal.mul_mem_right _ _ hl) (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_)
    have hnu : ¬ IsUnit (((frobeniusEquiv (Ob l) l).symm ^ i) (s.coeff i)) := fun hu =>
      hs i ((isUnit_map_iff ((frobeniusEquiv (Ob l) l).symm ^ i) _).1 hu)
    obtain ⟨k, d, hd⟩ := h4 _ hnu
    rw [hd, map_mul]
    exact Ideal.mul_mem_right _ _ (hr k)

end CrystallineSemistableComparison.D
end
end
