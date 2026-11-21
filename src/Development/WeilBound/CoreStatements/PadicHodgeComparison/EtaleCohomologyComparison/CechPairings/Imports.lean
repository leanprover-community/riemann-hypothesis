import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DoubleComplexMapMemTotal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DcColSurj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCochainFiltrationDecomposition

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace CrystallineSemistableComparison.ExtensionDiagram
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

def mk {Y : C ⥤ Type t} {q : ℕ} (c : ComposableArrows C q) (y : ∀ k, Y.obj (c.obj k))
    (h : ∀ {a b : Fin (q + 1)} (φ : a ⟶ b), Y.map (c.map φ) (y a) = y b) : ComposableArrows Y.Elements q where
  obj k := ⟨c.obj k, y k⟩
  map φ := ⟨c.map φ, h φ⟩
  map_id k := Subtype.ext (c.map_id k)
  map_comp φ ψ := Subtype.ext (c.map_comp φ ψ)

theorem mk_congr {Y : C ⥤ Type t} (F : C ⥤ ModuleCat.{w} R) {q : ℕ} (f : Cn (elF Y F) q) (c : ComposableArrows C q)
    {y y' : ∀ k, Y.obj (c.obj k)} h h' (e : y = y') :
    @Eq (F.obj (c.obj (Fin.last q))) (f (mk c y h)) (f (mk c y' h')) := by
  subst e; rfl

variable {E' E : C ⥤ Type t} (p : E' ⟶ E) (hp : ∀ T, Function.Surjective (p.app T))

noncomputable def lft {q : ℕ} (c : ComposableArrows C q) (e : E.obj (c.obj 0)) (k : Fin (q + 1)) : E'.obj (c.obj k) :=
  E'.map (c.map (homOfLE (Fin.zero_le k))) (hp _ e).choose

theorem lft_map {q : ℕ} (c : ComposableArrows C q) (e : E.obj (c.obj 0)) {a b : Fin (q + 1)} (φ : a ⟶ b) :
    E'.map (c.map φ) (lft p hp c e a) = lft p hp c e b := by
  unfold lft
  rw [← Functor.map_comp_apply, ← c.map_comp]; rfl

theorem p_lft {q : ℕ} (c : ComposableArrows C q) (e : E.obj (c.obj 0)) (k : Fin (q + 1)) :
    p.app _ (lft p hp c e k) = E.map (c.map (homOfLE (Fin.zero_le k))) e := by
  unfold lft
  rw [NatTrans.naturality_apply, (hp _ e).choose_spec]

theorem p_el {q n : ℕ} (s : ComposableArrows (cech p n).Elements q) (k : Fin (q + 1)) (i : Fin (n + 1)) :
    E.map (s.map (homOfLE (Fin.zero_le k))).1 (p.app _ ((s.obj 0).2.1 0)) = p.app _ ((s.obj k).2.1 i) := by
  rw [← NatTrans.naturality_apply, ← (s.obj k).2.2 0 i]
  exact congrArg (fun z => p.app _ (z.1 0)) (s.map (homOfLE (Fin.zero_le k))).2

noncomputable def extY {q n : ℕ} (s : ComposableArrows (cech p n).Elements q) (k : Fin (q + 1)) :
    (cech p (n + 1)).obj (s.obj k).1 :=
  ⟨Fin.cons (lft p hp (s ⋙ CategoryOfElements.π _) (p.app _ ((s.obj 0).2.1 0)) k) (s.obj k).2.1, by
    have h : ∀ i : Fin (n + 2), p.app _ ((Fin.cons (lft p hp (s ⋙ CategoryOfElements.π _) (p.app _ ((s.obj 0).2.1 0)) k)
        (s.obj k).2.1 : Fin (n + 2) → E'.obj (s.obj k).1) i) = p.app _ ((s.obj k).2.1 0) := by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact (p_lft p hp (s ⋙ CategoryOfElements.π _) _ k).trans (p_el p s k 0)
      · exact (s.obj k).2.2 i 0
    intro i j
    rw [h i, h j]⟩

theorem extY_map {q n : ℕ} (s : ComposableArrows (cech p n).Elements q) {a b : Fin (q + 1)} (φ : a ⟶ b) :
    (cech p (n + 1)).map (s.map φ).1 (extY p hp s a) = extY p hp s b := by
  refine Subtype.ext (funext fun i => ?_)
  refine Fin.cases ?_ (fun i => ?_) i
  · exact lft_map p hp (s ⋙ CategoryOfElements.π _) _ φ
  · exact congrArg (fun z => z.1 i) (s.map φ).2

noncomputable def ext {q n : ℕ} (s : ComposableArrows (cech p n).Elements q) : ComposableArrows (cech p (n + 1)).Elements q :=
  mk (s ⋙ CategoryOfElements.π _) (extY p hp s) (extY_map p hp s)

variable (F : C ⥤ ModuleCat.{w} R)

theorem dh_apply {q n : ℕ} (f : Cn (elF (cech p n) F) q) (s : ComposableArrows (cech p (n + 1)).Elements q) :
    @Eq (F.obj (s.obj (Fin.last q)).1) ((cechCos p F).dcx.dh n q f s)
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • f (s ⋙ CategoryOfElements.map (cechMap p i.succAbove))) := by
  have := congrFun (Cos.d_apply ((cechCos p F).cos q) n f) s
  rw [Finset.sum_apply] at this
  exact this

theorem ext_zero {q n : ℕ} (f : Cn (elF (cech p n) F) q) (s : ComposableArrows (cech p n).Elements q) :
    @Eq (F.obj (s.obj (Fin.last q)).1) (f (ext p hp s ⋙ CategoryOfElements.map (cechMap p (0 : Fin (n + 2)).succAbove))) (f s) :=
  rfl

theorem ext_succ {q n : ℕ} (f : Cn (elF (cech p (n + 1)) F) q) (s : ComposableArrows (cech p (n + 1)).Elements q) (i : Fin (n + 2)) :
    @Eq (F.obj (s.obj (Fin.last q)).1) (f (ext p hp s ⋙ CategoryOfElements.map (cechMap p i.succ.succAbove)))
      (f (ext p hp (s ⋙ CategoryOfElements.map (cechMap p i.succAbove)))) := by
  refine mk_congr F f (s ⋙ CategoryOfElements.π _)
    (y := fun k => (cechMap p i.succ.succAbove).app _ (extY p hp s k))
    (y' := fun k => extY p hp (s ⋙ CategoryOfElements.map (cechMap p i.succAbove)) k) _ _ (funext fun k => Subtype.ext (funext fun j => ?_))
  refine Fin.cases ?_ (fun j => ?_) j
  · change (extY p hp s k).1 (i.succ.succAbove 0) = _
    rw [Fin.succ_succAbove_zero]
    exact congrArg (fun e => lft p hp (s ⋙ CategoryOfElements.π _) e k) ((s.obj 0).2.2 _ _)
  · change (extY p hp s k).1 (i.succ.succAbove j.succ) = _
    rw [Fin.succ_succAbove_succ]
    rfl

noncomputable def ext0 {q : ℕ} (s : ComposableArrows E.Elements q) : ComposableArrows (cech p 0).Elements q :=
  mk (s ⋙ CategoryOfElements.π _) (fun k => ⟨fun _ => lft p hp (s ⋙ CategoryOfElements.π _) (s.obj 0).2 k, fun _ _ => rfl⟩)
    fun φ => Subtype.ext (funext fun _ => lft_map p hp (s ⋙ CategoryOfElements.π _) _ φ)

end CrystallineSemistableComparison.ExtensionDiagram

open CrystallineSemistableComparison.ExtensionDiagram in
theorem CrystallineSemistableComparison.P.cech_row : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R), (∀ T, Function.Surjective (p.app T)) → ∀ q, ((cechCos p F).dcx.row q).ResUpTo 1 ((cechAugRow p F).ε q) := by
  intro R _ C _ E' E p F hp q
  refine ⟨(cechAugRow p F).hε q, fun g hg => ?_, fun f hf => ?_, fun n f hf => ?_⟩
  · rw [one_smul]
    funext s
    have h1 := congrFun hg (ext0 p hp s)
    refine Eq.trans ?_ h1
    refine mk_congr F g (s ⋙ CategoryOfElements.π _) (y := fun k => (s.obj k).2)
      (y' := fun k => p.app _ (lft p hp (s ⋙ CategoryOfElements.π _) (s.obj 0).2 k)) (fun φ => (s.map φ).2) _ (funext fun k => ?_)
    rw [p_lft]
    exact (s.map (homOfLE (Fin.zero_le k))).2.symm
  · refine ⟨fun s => f (ext0 p hp s), ?_⟩
    rw [one_smul]
    funext s
    have h1 := (dh_apply p F f (ext p hp s)).symm.trans (congrFun hf (ext p hp s))
    rw [Fin.sum_univ_two] at h1
    have h2 : @Eq (F.obj (s.obj (Fin.last q)).1) (f (ext p hp s ⋙ CategoryOfElements.map (cechMap p (1 : Fin 2).succAbove)))
        (f (ext0 p hp (s ⋙ CategoryOfElements.map (cechAug p 0)))) := by
      refine mk_congr F f (s ⋙ CategoryOfElements.π _)
        (y := fun k => (cechMap p (1 : Fin 2).succAbove).app _ (extY p hp s k)) _ _ (funext fun k => Subtype.ext (funext fun j => ?_))
      obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) _ _
      rfl
    erw [ext_zero p hp F f s, h2] at h1
    change f (ext0 p hp (s ⋙ CategoryOfElements.map (cechAug p 0))) = f s
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at h1
    exact (add_neg_eq_zero.1 h1).symm
  · refine ⟨fun s => f (ext p hp s), ?_⟩
    rw [one_smul]
    funext s
    have h1 := (dh_apply p F f (ext p hp s)).symm.trans (congrFun hf (ext p hp s))
    rw [Fin.sum_univ_succ] at h1
    erw [ext_zero p hp F f s] at h1
    refine (dh_apply p F _ s).trans ?_
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib] at h1
    refine Eq.trans ?_ (add_neg_eq_zero.1 h1).symm
    exact Finset.sum_congr rfl fun i _ => congrArg _ (ext_succ p hp F f s i).symm

theorem CrystallineSemistableComparison.P.cech_desc : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R), (∀ T, Function.Surjective (p.app T)) → ∀ n, Function.Bijective ((cechAugRow p F).edge.mapH n) := by
  intro R _ C _ E' E p F hp n
  have := CrystallineSemistableComparison.P.dc_row (cechAugRow p F) 1 (CrystallineSemistableComparison.P.cech_row p F hp) n
  rw [one_pow] at this
  exact (CrystallineSemistableComparison.P.upTo_alg _ (LinearMap.id (R := R)) 1 1).2.2.2.2.1 this
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
namespace CrystallineSemistableComparison.Auxfi

section Gen
variable {R : Type} [CommRing R]

theorem exact_one {M : Type w} {N : Type w'} {P : Type w''} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P} (h : ExactUpTo (1 : R) f g) (s : R) :
    ExactUpTo s f g := by
  intro y hy
  obtain ⟨x, hx⟩ := h y hy
  exact ⟨s • x, by rw [map_smul, hx, one_smul]⟩

theorem tr_exact {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) (hφ : ∀ n, Function.Bijective (φ.f n))
    (s : R) (m : ℕ) (h : ExactUpTo s (L.d m) (L.d (m + 1))) : ExactUpTo s (K.d m) (K.d (m + 1)) := by
  intro y hy
  have h1 : L.d (m + 1) (φ.f (m + 1) y) = 0 := by rw [φ.comm, hy, map_zero]
  obtain ⟨x', hx'⟩ := h _ h1
  obtain ⟨x, rfl⟩ := (hφ m).2 x'
  refine ⟨x, (hφ (m + 1)).1 ?_⟩
  rw [← φ.comm, hx', LinearMap.map_smulₛₗ]; rfl

theorem tr_aug {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R)) (hφ : ∀ n, Function.Bijective (φ.f n))
    {M : Type w''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0) (ε' : M →ₗ[R] L.X 0)
    (he : ∀ x, φ.f 0 (ε x) = ε' x) (s : R) :
    (InjUpTo s ε' → InjUpTo s ε) ∧ (ExactUpTo s ε' (L.d 0) → ExactUpTo s ε (K.d 0)) := by
  refine ⟨fun h x hx => h x (by rw [← he, hx, map_zero]), fun h y hy => ?_⟩
  have h1 : L.d 0 (φ.f 0 y) = 0 := by rw [φ.comm, hy, map_zero]
  obtain ⟨x, hx⟩ := h _ h1
  refine ⟨x, (hφ 0).1 ?_⟩
  rw [he, hx, LinearMap.map_smulₛₗ]; rfl

end Gen

end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Aug
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem d_aug (F : C ⥤ ModuleCat.{w} R) {M : Type w'} [AddCommGroup M] [Module R M] (e : ∀ T : C, M →ₗ[R] F.obj T)
    (he : ∀ {X Y : C} (ψ : X ⟶ Y) (x : M), (F.map ψ).hom (e X x) = e Y x) (x : M) :
    d F 0 (aug F e x) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (GlobalTheory.CatH.toLast i s)).hom (aug F e x (GlobalTheory.CatH.face i s)) = 0
  rw [Fin.sum_univ_two]
  change (-1 : ℤ) ^ 0 • (F.map (GlobalTheory.CatH.toLast 0 s)).hom (e _ x) + (-1 : ℤ) ^ 1 • (F.map (GlobalTheory.CatH.toLast 1 s)).hom (e _ x) = 0
  rw [he, he]; simp

end Aug
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Pw
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R)

theorem el_hom {A : C} {X Y : (pts j A).Elements} (ψ : X ⟶ Y) : (show A ⟶ j.obj X.1 from X.2) ≫ j.map ψ.1 = Y.2 := ψ.2

theorem ptsAug_d (A : C) (x : F.obj A) : d (elF (pts j A) (j ⋙ F)) 0 (ptsAug j F A x) = 0 := by
  refine d_aug _ _ (fun {X Y} ψ x => ?_) x
  change (F.map (j.map ψ.1)).hom ((F.map (show A ⟶ j.obj X.1 from X.2)).hom x) = (F.map (show A ⟶ j.obj Y.1 from Y.2)).hom x
  have h := el_hom j ψ
  refine Eq.trans ?_ (congrArg (fun m => (F.map m).hom x) h)
  rw [F.map_comp]; rfl

def pmap {A : C} (P : Powers j A) : pts j P.B ⟶ pts j A := Functor.whiskerLeft j (coyoneda.map P.f.op)

end Pw
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section S0
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R)

theorem map_iso_inj {X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Injective (F.map f).hom := by
  intro y z h
  have := congrArg (F.map (inv f)).hom h
  simpa only [← ModuleCat.comp_apply, ← F.map_comp, IsIso.hom_inv_id, F.map_id, ModuleCat.id_apply] using this

theorem map_iso_surj {X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Surjective (F.map f).hom := by
  intro y
  refine ⟨(F.map (inv f)).hom y, ?_⟩
  simp only [← ModuleCat.comp_apply, ← F.map_comp, IsIso.inv_hom_id, F.map_id, ModuleCat.id_apply]

theorem ptsAug_eval (A : C) (x : F.obj A) (X : (pts j A).Elements) :
    ptsAug j F A x (ComposableArrows.mk₀ X) = (F.map (show A ⟶ j.obj X.1 from X.2)).hom x := rfl

theorem cechDifferential_zero {A : C} (P : Powers j A) (x : F.obj (P.K 0)) : P.dK j F 0 x = (F.map (P.δ 0 0)).hom x := by
  simp [Powers.dK]

theorem s0a (I : Ideal R) {A : C} (P : Powers j A) (hG : P.Good j F I) (a : R) (ha : a ∈ I) :
    InjUpTo (a ^ 2) (ptsAug j F A) := by
  intro x hx
  obtain ⟨-, hex, t0, g, -, halm⟩ := hG
  have h1 : (F.map g).hom ((F.map P.f).hom x) = 0 := by
    have := congrFun hx (ComposableArrows.mk₀ (⟨t0, P.f ≫ g⟩ : (pts j A).Elements))
    rw [ptsAug_eval, F.map_comp] at this
    exact this
  have h2 := (halm a ha).1 _ h1
  have h3 : P.dK j F 0 ((F.map (P.a 0)).hom (a • x)) = 0 := by
    rw [cechDifferential_zero, ← ModuleCat.comp_apply, ← F.map_comp, P.aδ, ← P.w 1 0, F.map_comp, ModuleCat.comp_apply, map_smul, h2,
      map_zero]
  have h4 := (hex a ha).1 _ h3
  rw [← map_smul] at h4
  have := P.iso0
  apply map_iso_inj F (P.a 0)
  rw [pow_two, mul_smul, h4, map_zero]

end S0
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section S0b
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R)

noncomputable def initB {B : C} (t0 : T) (g : B ⟶ j.obj t0) (hg : ∀ (t : T) (y : B ⟶ j.obj t), ∃! φ : t0 ⟶ t, g ≫ j.map φ = y) :
    Limits.IsInitial ((pts j B).elementsMk t0 g) :=
  Limits.IsInitial.ofUniqueHom (fun (Y : (pts j B).Elements) => ⟨(hg Y.1 Y.2).exists.choose, (hg Y.1 Y.2).exists.choose_spec⟩)
    (fun (Y : (pts j B).Elements) m => Subtype.ext ((hg Y.1 Y.2).unique m.2 (hg Y.1 Y.2).exists.choose_spec))

theorem cmk (E : T ⥤ Type v) (s : ComposableArrows E.Elements 0) : s = ComposableArrows.mk₀ (s.obj 0) :=
  ComposableArrows.ext₀ rfl

theorem c_eq {A : C} (c : Cn (elF (pts j A) (j ⋙ F)) 0) (t : T) {z z' : A ⟶ j.obj t} (h : z = z') :
    c (ComposableArrows.mk₀ ((pts j A).elementsMk t z)) = c (ComposableArrows.mk₀ ((pts j A).elementsMk t z')) := by
  subst h; rfl

theorem cechDifferential_one_inclusion {A : C} (P : Powers j A) (b : F.obj P.B) :
    P.dK j F 1 ((F.map (P.ι 1 0)).hom b) = (F.map (P.ι 2 1)).hom b - (F.map (P.ι 2 0)).hom b := by
  have e0 : (F.map (P.δ 1 0)).hom ((F.map (P.ι 1 0)).hom b) = (F.map (P.ι 2 1)).hom b := by
    rw [← ModuleCat.comp_apply, ← F.map_comp, P.ιδ]; rfl
  have e1 : (F.map (P.δ 1 1)).hom ((F.map (P.ι 1 0)).hom b) = (F.map (P.ι 2 0)).hom b := by
    rw [← ModuleCat.comp_apply, ← F.map_comp, P.ιδ]; rfl
  simp [Powers.dK, sub_eq_add_neg, e0, e1]

theorem s0b (I : Ideal R) {A : C} (P : Powers j A) (hG : P.Good j F I)
    (h0a : ∀ s ∈ I, InjUpTo s (ptsAug j F (P.K 2))) (a : R) (ha : a ∈ I) :
    ExactUpTo (a ^ 3) (ptsAug j F A) (d (elF (pts j A) (j ⋙ F)) 0) := by
  intro c hc
  obtain ⟨hsurj, hex, t0, g, hg, halm⟩ := hG
  let Φ := (elMor (pmap j P) (j ⋙ F)).hom
  have hc' : d (elF (pts j P.B) (j ⋙ F)) 0 (Φ.f 0 c) = 0 := by
    rw [Φ.comm, show (cx (elF (pts j A) (j ⋙ F))).d 0 c = 0 from hc, map_zero]
  have hI := initB j t0 g hg
  obtain ⟨m, hm⟩ := (CrystallineSemistableComparison.P.initial (elF (pts j P.B) (j ⋙ F)) _ hI).2.2.1 _ hc'
  obtain ⟨b, hb⟩ := (halm a ha).2 (show F.obj (j.obj t0) from m)
  have key : ∀ (t : T) (y : P.B ⟶ j.obj t), (F.map y).hom b =
      a • c (ComposableArrows.mk₀ ((pts j A).elementsMk t (P.f ≫ y))) := by
    intro t y
    let ψ := hI.to ((pts j P.B).elementsMk t y)
    have hψ : g ≫ j.map ψ.1 = y := ψ.2
    have e1 := congrFun hm (ComposableArrows.mk₀ ((pts j P.B).elementsMk t y))
    rw [one_smul] at e1
    change (F.map (j.map ψ.1)).hom m = c (ComposableArrows.mk₀ ((pts j P.B).elementsMk t y) ⋙ CategoryOfElements.map (pmap j P)) at e1
    have e2 : ComposableArrows.mk₀ ((pts j P.B).elementsMk t y) ⋙ CategoryOfElements.map (pmap j P) =
        ComposableArrows.mk₀ ((pts j A).elementsMk t (P.f ≫ y)) := ComposableArrows.ext₀ rfl
    have e3 : HEq (c (ComposableArrows.mk₀ ((pts j P.B).elementsMk t y) ⋙ CategoryOfElements.map (pmap j P)))
        (c (ComposableArrows.mk₀ ((pts j A).elementsMk t (P.f ≫ y)))) := by rw [e2]
    rw [← e1.trans (eq_of_heq e3)]
    have e4 : (F.map y).hom b = (F.map (j.map ψ.1)).hom ((F.map g).hom b) := by
      rw [← ModuleCat.comp_apply, ← F.map_comp, hψ]
    rw [e4, hb]
    exact map_smul _ _ _
  have hb1 : ptsAug j F (P.K 2) (P.dK j F 1 ((F.map (P.ι 1 0)).hom b)) = 0 := by
    rw [cechDifferential_one_inclusion]
    funext s
    rw [cmk _ s]
    change (F.map (s.obj 0).2).hom ((F.map (P.ι 2 1)).hom b - (F.map (P.ι 2 0)).hom b) = 0
    rw [map_sub, ← ModuleCat.comp_apply, ← F.map_comp, ← ModuleCat.comp_apply, ← F.map_comp, key, key,
      c_eq j F c _ (by rw [← Category.assoc, P.w] : P.f ≫ P.ι 2 1 ≫ (s.obj 0).2 = P.a 2 ≫ (s.obj 0).2),
      c_eq j F c _ (by rw [← Category.assoc, P.w] : P.f ≫ P.ι 2 0 ≫ (s.obj 0).2 = P.a 2 ≫ (s.obj 0).2), sub_self]
  have h2 := h0a a ha _ hb1
  rw [← map_smul] at h2
  obtain ⟨x0, hx0⟩ := (hex a ha).2 0 _ h2
  have := P.iso0
  have := P.iso1
  obtain ⟨x, rfl⟩ := map_iso_surj F (P.a 0) x0
  have hfx : (F.map P.f).hom x = a • a • b := by
    apply map_iso_inj F (P.ι 1 0)
    rw [← ModuleCat.comp_apply, ← F.map_comp, P.w, ← P.aδ 0 0, F.map_comp, ModuleCat.comp_apply, ← cechDifferential_zero, hx0,
      map_smul, map_smul]
  refine ⟨x, ?_⟩
  funext s
  rw [cmk _ s]
  obtain ⟨y, hy⟩ := hsurj (s.obj 0).1 (s.obj 0).2
  change (F.map (s.obj 0).2).hom x = a ^ 3 • c (ComposableArrows.mk₀ ((pts j A).elementsMk (s.obj 0).1 (s.obj 0).2))
  rw [← c_eq j F c _ hy, ← hy, F.map_comp, ModuleCat.comp_apply, hfx, map_smul, map_smul, key, smul_smul, smul_smul,
    pow_three, mul_assoc]

end S0b
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Col
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R) {A : C} (P : Powers j A)

theorem cech_compat {n : ℕ} (X : (cech (pmap j P) n).Elements) (i : Fin (n + 1)) :
    P.f ≫ X.2.1 i = P.f ≫ X.2.1 0 := X.2.2 i 0

noncomputable def zz {n : ℕ} (X : (cech (pmap j P) n).Elements) : P.K (n + 1) ⟶ j.obj X.1 :=
  (P.univ (n + 1) X.1 (P.f ≫ X.2.1 0) X.2.1 (cech_compat j P X)).exists.choose

theorem zz_spec {n : ℕ} (X : (cech (pmap j P) n).Elements) :
    P.a (n + 1) ≫ zz j P X = P.f ≫ X.2.1 0 ∧ ∀ i, P.ι (n + 1) i ≫ zz j P X = X.2.1 i :=
  (P.univ (n + 1) X.1 (P.f ≫ X.2.1 0) X.2.1 (cech_compat j P X)).exists.choose_spec

theorem zz_uniq {n : ℕ} (X : (cech (pmap j P) n).Elements) (z : P.K (n + 1) ⟶ j.obj X.1)
    (h1 : P.a (n + 1) ≫ z = P.f ≫ X.2.1 0) (h2 : ∀ i, P.ι (n + 1) i ≫ z = X.2.1 i) : z = zz j P X :=
  (P.univ (n + 1) X.1 (P.f ≫ X.2.1 0) X.2.1 (cech_compat j P X)).unique ⟨h1, h2⟩ (zz_spec j P X)

theorem cech_hom {n : ℕ} {X Y : (cech (pmap j P) n).Elements} (ψ : X ⟶ Y) (i : Fin (n + 1)) :
    X.2.1 i ≫ j.map ψ.1 = Y.2.1 i := congrFun (congrArg Subtype.val ψ.2) i

theorem zz_nat {n : ℕ} {X Y : (cech (pmap j P) n).Elements} (ψ : X ⟶ Y) :
    zz j P X ≫ j.map ψ.1 = zz j P Y := by
  apply zz_uniq
  · rw [← Category.assoc, (zz_spec j P X).1, Category.assoc, cech_hom j P ψ]
  · intro i; rw [← Category.assoc, (zz_spec j P X).2, cech_hom j P ψ]

end Col
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Col2
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R) {A : C} (P : Powers j A)

noncomputable def eta (n : ℕ) : F.obj (P.K (n + 1)) →ₗ[R] Cn (elF (cech (pmap j P) n) (j ⋙ F)) 0 :=
  aug (elF (cech (pmap j P) n) (j ⋙ F)) fun X => (F.map (zz j P X)).hom

theorem eta_d (n : ℕ) (x : F.obj (P.K (n + 1))) : d (elF (cech (pmap j P) n) (j ⋙ F)) 0 (eta j F P n x) = 0 := by
  refine d_aug _ _ (fun {X Y} ψ x => ?_) x
  change (F.map (j.map ψ.1)).hom ((F.map (zz j P X)).hom x) = (F.map (zz j P Y)).hom x
  rw [← zz_nat j P ψ, F.map_comp]; rfl

noncomputable def cosK : Cos.{w} R where
  X n := F.obj (P.K (n + 1))
  δ n i := (F.map (P.δ (n + 1) i)).hom
  rel n k i x := by
    rw [← ModuleCat.comp_apply, ← F.map_comp, P.rel (n + 1) k i, F.map_comp]; rfl

theorem zz_δ (n : ℕ) (i : Fin (n + 2)) (X : (cech (pmap j P) (n + 1)).Elements) :
    zz j P ((CategoryOfElements.map (cechMap (pmap j P) i.succAbove)).obj X) = P.δ (n + 1) i ≫ zz j P X := by
  symm
  refine zz_uniq j P ((CategoryOfElements.map (cechMap (pmap j P) i.succAbove)).obj X) (P.δ (n + 1) i ≫ zz j P X) ?_ ?_
  · change P.a (n + 1) ≫ P.δ (n + 1) i ≫ zz j P X = P.f ≫ X.2.1 (i.succAbove 0)
    rw [← Category.assoc, P.aδ, (zz_spec j P X).1]
    exact (cech_compat j P X _).symm
  · intro k
    change P.ι (n + 1) k ≫ P.δ (n + 1) i ≫ zz j P X = X.2.1 (i.succAbove k)
    rw [← Category.assoc, P.ιδ, (zz_spec j P X).2]

end Col2
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Col3
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R) {A : C} (P : Powers j A)

noncomputable def augc : DCx.AugCol (cosK j F P).cx (cechCos (pmap j P) (j ⋙ F)).dcx where
  η p := eta j F P p
  hη p x := eta_d j F P p x
  comm p x := by
    funext s
    change (Cos.d ((cechCos (pmap j P) (j ⋙ F)).cos 0) p (eta j F P p x)) s =
      (F.map (zz j P (s.obj (Fin.last 0)))).hom (Cos.d (cosK j F P) p x)
    rw [Cos.d_apply, Cos.d_apply, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, map_zsmul]
    congr 1
    change (F.map (zz j P ((CategoryOfElements.map (cechMap (pmap j P) i.succAbove)).obj (s.obj (Fin.last 0))))).hom x =
      (F.map (zz j P (s.obj (Fin.last 0)))).hom ((F.map (P.δ (p + 1) i)).hom x)
    rw [zz_δ, F.map_comp]; rfl

end Col3
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Col4
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R) {A : C} (P : Powers j A)

def uK (n : ℕ) : pts j (P.K (n + 1)) ⟶ cech (pmap j P) n where
  app t := TypeCat.ofHom fun z => ⟨fun i => P.ι (n + 1) i ≫ z, fun i k => by
    change P.f ≫ P.ι (n + 1) i ≫ z = P.f ≫ P.ι (n + 1) k ≫ z
    rw [← Category.assoc, ← Category.assoc, P.w, P.w]⟩
  naturality X Y φ := by
    ext z
    exact Subtype.ext (funext fun i => (Category.assoc (P.ι (n + 1) i) z (j.map φ)).symm)

theorem uK_bij (n : ℕ) (t : T) : Function.Bijective ((uK j P n).app t) := by
  constructor
  · intro z z' h
    have h' : ∀ i, P.ι (n + 1) i ≫ z = P.ι (n + 1) i ≫ z' := fun i => congrFun (congrArg Subtype.val h) i
    have hx : ∀ i, P.f ≫ P.ι (n + 1) i ≫ z' = P.a (n + 1) ≫ z' := fun i => by rw [← Category.assoc, P.w]
    exact (P.univ (n + 1) t (P.a (n + 1) ≫ z') (fun i => P.ι (n + 1) i ≫ z') hx).unique
      ⟨by rw [← P.w (n + 1) 0, Category.assoc, h' 0, ← Category.assoc], h'⟩ ⟨rfl, fun _ => rfl⟩
  · intro y
    refine ⟨zz j P ((cech (pmap j P) n).elementsMk t y), Subtype.ext (funext fun i => ?_)⟩
    exact (zz_spec j P ((cech (pmap j P) n).elementsMk t y)).2 i

theorem uK_eta (n : ℕ) (x : F.obj (P.K (n + 1))) :
    (elMor (uK j P n) (j ⋙ F)).hom.f 0 (eta j F P n x) = ptsAug j F (P.K (n + 1)) x := by
  funext s
  change (F.map (zz j P ((CategoryOfElements.map (uK j P n)).obj (s.obj (Fin.last 0))))).hom x =
    (F.map (show P.K (n + 1) ⟶ j.obj (s.obj (Fin.last 0)).1 from (s.obj (Fin.last 0)).2)).hom x
  congr 3
  symm
  refine zz_uniq j P ((CategoryOfElements.map (uK j P n)).obj (s.obj (Fin.last 0))) _ ?_ (fun i => rfl)
  change P.a (n + 1) ≫ _ = P.f ≫ P.ι (n + 1) 0 ≫ _
  rw [← Category.assoc, P.w]

end Col4
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Step
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R) {A : C} (P : Powers j A)

noncomputable def init0 (t0 : T) (g : P.B ⟶ j.obj t0) (hg : ∀ (t : T) (y : P.B ⟶ j.obj t), ∃! φ : t0 ⟶ t, g ≫ j.map φ = y) :
    Limits.IsInitial ((cech (pmap j P) 0).elementsMk t0 ⟨fun _ => g, fun _ _ => rfl⟩) :=
  Limits.IsInitial.ofUniqueHom
    (fun (Y : (cech (pmap j P) 0).Elements) => ⟨(hg Y.1 (Y.2.1 0)).exists.choose, Subtype.ext (funext fun i => by
      rw [Fin.fin_one_eq_zero i]; exact (hg Y.1 (Y.2.1 0)).exists.choose_spec)⟩)
    (fun (Y : (cech (pmap j P) 0).Elements) m =>
      Subtype.ext ((hg Y.1 (Y.2.1 0)).unique (cech_hom j P m 0) (hg Y.1 (Y.2.1 0)).exists.choose_spec))

theorem cech_column_zero_exact (t0 : T) (g : P.B ⟶ j.obj t0) (hg : ∀ (t : T) (y : P.B ⟶ j.obj t), ∃! φ : t0 ⟶ t, g ≫ j.map φ = y)
    (q : ℕ) (s : R) :
    ExactUpTo s ((cx (elF (cech (pmap j P) 0) (j ⋙ F))).d q) ((cx (elF (cech (pmap j P) 0) (j ⋙ F))).d (q + 1)) :=
  exact_one ((CrystallineSemistableComparison.P.initial (elF (cech (pmap j P) 0) (j ⋙ F)) _ (init0 j P t0 g hg)).2.2.2 q) s

end Step
end CrystallineSemistableComparison.Auxfi

namespace CrystallineSemistableComparison.Auxfi
section Step2
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
  (F : C ⥤ ModuleCat.{w} R)

theorem sstep (I : Ideal R) {A : C} (P : Powers j A) (hG : P.Good j F I) (n : ℕ)
    (IH : ∀ m < n, ∀ A' : C, ∀ s ∈ I,
      ExactUpTo s ((cx (elF (pts j A') (j ⋙ F))).d m) ((cx (elF (pts j A') (j ⋙ F))).d (m + 1)))
    (h0a : ∀ A' : C, ∀ s ∈ I, InjUpTo s (ptsAug j F A'))
    (h0b : ∀ A' : C, ∀ s ∈ I, ExactUpTo s (ptsAug j F A') ((cx (elF (pts j A') (j ⋙ F))).d 0))
    (a : R) (ha : a ∈ I) :
    ExactUpTo (a ^ (n + 4)) ((cx (elF (pts j A) (j ⋙ F))).d n) ((cx (elF (pts j A) (j ⋙ F))).d (n + 1)) := by
  obtain ⟨hsurj, hex, t0, g, hg, halm⟩ := hG
  have hbφ : ∀ m q, Function.Bijective ((elMor (uK j P m) (j ⋙ F)).hom.f q) :=
    fun m => CrystallineSemistableComparison.P.el_iso (uK j P m) (j ⋙ F) (uK_bij j P m)
  have hcol : ∀ p q, p + q + 1 = n + 1 → ExactUpTo a ((cechCos (pmap j P) (j ⋙ F)).dcx.dv p q)
      ((cechCos (pmap j P) (j ⋙ F)).dcx.dv p (q + 1)) := by
    intro p q hpq
    rcases p with _ | p
    · exact cech_column_zero_exact j F P t0 g hg q a
    · exact tr_exact _ (hbφ (p + 1)) a q (IH q (by omega) (P.K (p + 2)) a ha)
  have hη : ExactUpTo a ((augc j F P).η (n + 1)) ((cechCos (pmap j P) (j ⋙ F)).dcx.dv (n + 1) 0) :=
    (tr_aug _ (hbφ (n + 1)) (eta j F P (n + 1)) (ptsAug j F (P.K (n + 2))) (uK_eta j F P (n + 1)) a).2 (h0b _ a ha)
  have hinj : InjUpTo a ((augc j F P).η (n + 2)) :=
    (tr_aug _ (hbφ (n + 2)) (eta j F P (n + 2)) (ptsAug j F (P.K (n + 3))) (uK_eta j F P (n + 2)) a).1 (h0a _ a ha)
  have hs := CrystallineSemistableComparison.P.dc_col_surj (augc j F P) a (n + 1) hcol hη hinj
  have hps : ∀ t, Function.Surjective ((pmap j P).app t) := fun t x => hsurj t x
  have hbij := CrystallineSemistableComparison.P.cech_desc (pmap j P) (j ⋙ F) hps (n + 1)
  intro y hy
  obtain ⟨xa, hxa⟩ := hs ((cechAugRow (pmap j P) (j ⋙ F)).edge.mapH (n + 1) ((cx (elF (pts j A) (j ⋙ F))).cls y hy))
  obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cosK j F P).cx (n + 1)).1 xa
  obtain ⟨b', hb'⟩ := (hex a ha).2 (n + 1) b hb
  have hab : a • (cosK j F P).cx.cls b hb = 0 := by
    rw [← (CrystallineSemistableComparison.P.cls_surj _ (n + 1)).2.2.2.2 a b hb (by rw [map_smul, hb, smul_zero])]
    rw [(CrystallineSemistableComparison.P.cls_surj _ (n + 1)).2.1]
    exact ⟨b', hb'⟩
  have hy' : (cx (elF (pts j A) (j ⋙ F))).d (n + 1) (a ^ (n + 4) • y) = 0 := by rw [map_smul, hy, smul_zero]
  have h0 : (cechAugRow (pmap j P) (j ⋙ F)).edge.mapH (n + 1) ((cx (elF (pts j A) (j ⋙ F))).cls _ hy') = 0 := by
    rw [(CrystallineSemistableComparison.P.cls_surj _ (n + 1)).2.2.2.2 _ y hy, map_smul, pow_succ', mul_smul, ← hxa, ← map_smul, hab, map_zero]
  have h1 := hbij.1 (h0.trans (map_zero _).symm)
  rw [(CrystallineSemistableComparison.P.cls_surj _ (n + 1)).2.1] at h1
  obtain ⟨x, hx⟩ := h1
  exact ⟨x, hx⟩

end Step2
end CrystallineSemistableComparison.Auxfi

theorem CrystallineSemistableComparison.P.induct : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C) (F : C ⥤ ModuleCat.{w} R) (I : Ideal R), (∀ N : ℕ, I ≤ Ideal.span ((fun a => a ^ N) '' (I : Set R))) → (∀ A : C, ∃ P : Powers j A, P.Good j F I) → ∀ (A : C), ∀ s ∈ I, (cx (elF (pts j A) (j ⋙ F))).ResUpTo s (ptsAug j F A) := by
  intro R _ C _ T _ j F I hI hgood
  choose P hP using hgood
  have h0a : ∀ A : C, ∀ s ∈ I, InjUpTo s (ptsAug j F A) := fun A =>
    (CrystallineSemistableComparison.P.pow_upTo I hI 2 (ptsAug j F A) ((cx (elF (pts j A) (j ⋙ F))).d 0)).1
      (fun a ha => CrystallineSemistableComparison.Auxfi.s0a j F I (P A) (hP A) a ha)
  have h0b : ∀ A : C, ∀ s ∈ I, ExactUpTo s (ptsAug j F A) ((cx (elF (pts j A) (j ⋙ F))).d 0) := fun A =>
    (CrystallineSemistableComparison.P.pow_upTo I hI 3 (ptsAug j F A) ((cx (elF (pts j A) (j ⋙ F))).d 0)).2.2.2
      (fun a ha => CrystallineSemistableComparison.Auxfi.s0b j F I (P A) (hP A) (h0a _) a ha)
  have hn : ∀ n, ∀ A : C, ∀ s ∈ I,
      ExactUpTo s ((cx (elF (pts j A) (j ⋙ F))).d n) ((cx (elF (pts j A) (j ⋙ F))).d (n + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      exact fun A => (CrystallineSemistableComparison.P.pow_upTo I hI (n + 4) ((cx (elF (pts j A) (j ⋙ F))).d n)
        ((cx (elF (pts j A) (j ⋙ F))).d (n + 1))).2.2.2
        (fun a ha => CrystallineSemistableComparison.Auxfi.sstep j F I (P A) (hP A) n ih h0a h0b a ha)
  intro A s hs
  exact ⟨fun x => CrystallineSemistableComparison.Auxfi.ptsAug_d j F A x, h0a A s hs, h0b A s hs, fun n => hn n A s hs⟩
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

noncomputable section
namespace CrystallineSemistableComparison.RelativeAugmentedComplex
variable {R : Type} [CommRing R]

theorem terminal_res {D : Type u} [Category.{v} D] (Z : D) (hZ : Limits.IsTerminal Z) (M : ModuleCat.{w} R) :
    (cx ((Functor.const D).obj M)).ResUpTo 1 (aug ((Functor.const D).obj M) fun _ => (LinearMap.id : M →ₗ[R] M)) := by
  let P := (Functor.const (Discrete PUnit.{1})).obj M
  let F := (Functor.const D).obj M
  let a : Mor P F (RingHom.id R) := ⟨(Functor.const D).obj ⟨PUnit.unit⟩, fun _ => LinearMap.id, fun _ _ => rfl⟩
  let b : Mor F P (RingHom.id R) := ⟨(Functor.const _).obj Z, fun _ => LinearMap.id, fun _ _ => rfl⟩
  have hi : Limits.IsInitial (⟨PUnit.unit⟩ : Discrete PUnit.{1}) :=
    Limits.IsInitial.ofUniqueHom (fun _ => 𝟙 _) fun _ _ => Subsingleton.elim _ _
  have h0 := CrystallineSemistableComparison.P.initial P _ hi
  have h1 : ∀ n x, a.pull n (b.pull n x) = x := fun n x => by
    rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) b a n x).1, ← CrystallineSemistableComparison.P.prism (Mor.id F) (b.comp a)
      ⟨fun T => hZ.from T, fun _ _ _ => hZ.hom_ext _ _⟩ (fun _ _ => rfl) n x]
    exact (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) b a n x).2
  have h2 : ∀ n x, b.pull n (a.pull n x) = x := fun n x => by
    rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) a b n x).1, ← CrystallineSemistableComparison.P.prism (Mor.id P) (a.comp b)
      ⟨fun T => 𝟙 _, fun _ _ _ => Subsingleton.elim _ _⟩ (fun _ _ => rfl) n x]
    exact (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) a b n x).2
  have h3 : ∀ n, UpTo (1 : R) (a.hom.mapH n) := fun n =>
    (CrystallineSemistableComparison.P.upTo_alg _ (LinearMap.id (R := R)) 1 1).2.2.2.2.2 ⟨Function.LeftInverse.injective (h2 n), Function.RightInverse.surjective (h1 n)⟩
  have h4 := (CrystallineSemistableComparison.P.res_transfer a.hom _ 1 1 h3).1 h0
  rw [one_mul] at h4
  exact h4

variable {C : Type u} [Category.{v} C] {I : Type t} [Category.{t'} I] (π : C ⥤ I) (F : C ⥤ ModuleCat.{w} R)

def mkS {j : I} {q : ℕ} (c : ComposableArrows C q) (a : ∀ k, j ⟶ π.obj (c.obj k))
    (h : ∀ {k k' : Fin (q + 1)} (φ : k ⟶ k'), a k ≫ π.map (c.map φ) = a k') : ComposableArrows (StructuredArrow j π) q where
  obj k := StructuredArrow.mk (a k)
  map φ := StructuredArrow.homMk (c.map φ) (h φ)

theorem mkS_congr {j : I} {q : ℕ} (f : Cn (relF π F j) q) (c : ComposableArrows C q) {a a' : ∀ k, j ⟶ π.obj (c.obj k)}
    (h' : ∀ {k k' : Fin (q + 1)} (φ : k ⟶ k'), a' k ≫ π.map (c.map φ) = a' k')
    (e : a = a') : @Eq (F.obj (c.obj (Fin.last q))) (f (mkS π c a (e ▸ h'))) (f (mkS π c a' h')) := by
  subst e; rfl

def relCn (q : ℕ) : I ⥤ ModuleCat.{max u v w t'} R where
  obj i := ModuleCat.of R (Cn (relF π F i) q)
  map a := ModuleCat.ofHom ((relRes π F a).pullC q)
  map_id i := by
    ext f s
    exact mkS_congr π F f (s ⋙ StructuredArrow.proj _ _) (a := fun k => 𝟙 i ≫ (s.obj k).hom) (a' := fun k => (s.obj k).hom)
      (fun φ => StructuredArrow.w (s.map φ)) (funext fun k => Category.id_comp _)
  map_comp {i i' i''} a b := by
    ext f s
    exact mkS_congr π F f (s ⋙ StructuredArrow.proj _ _) (a := fun k => (a ≫ b) ≫ (s.obj k).hom)
      (a' := fun k => a ≫ b ≫ (s.obj k).hom) (fun φ => by
        rw [Category.assoc, Category.assoc]; exact congrArg (fun z => a ≫ b ≫ z) (StructuredArrow.w (s.map φ))) (funext fun k => Category.assoc _ _ _)

def relCx : CxF.{max u v w t'} I R where
  F := relCn π F
  δ q := { app := fun i => ModuleCat.ofHom (d (relF π F i) q)
           naturality := fun i i' a => by
             ext f
             exact (relRes π F a).d_pullC q f }
  dd q i := d_d (relF π F i) q

def relAugRow : DCx.AugRow (cx F) (relCx π F).dcx where
  ε q := aug (relCn π F q) fun i => (relAug π F i).pullC q
  hε q f := by
    funext s
    change ∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • (relAug π F (s.obj (Fin.last 1))).pullC q f = 0
    simp [Fin.sum_univ_two]
  comm q f := funext fun s => (relAug π F _).d_pullC q f

def mkO {Z : I} {p : ℕ} (i : ComposableArrows I p) (a : ∀ k, i.obj k ⟶ Z)
    (h : ∀ {k k' : Fin (p + 1)} (φ : k ⟶ k'), i.map φ ≫ a k' = a k) : ComposableArrows (Over Z) p where
  obj k := Over.mk (a k)
  map φ := Over.homMk (i.map φ) (h φ)

def st {j : I} {q : ℕ} (c : ComposableArrows C q) (a : j ⟶ π.obj (c.obj 0)) : ComposableArrows (StructuredArrow j π) q :=
  mkS π c (fun k => a ≫ π.map (c.map (homOfLE (Fin.zero_le k)))) fun φ => by
    rw [Category.assoc, ← π.map_comp, ← c.map_comp]; rfl

theorem st_w {j : I} {q : ℕ} (c : ComposableArrows C q) (a : j ⟶ π.obj (c.obj 0)) {k k' : Fin (q + 1)} (φ : k ⟶ k') :
    (a ≫ π.map (c.map (homOfLE (Fin.zero_le k)))) ≫ π.map (c.map φ) = a ≫ π.map (c.map (homOfLE (Fin.zero_le k'))) := by
  rw [Category.assoc, ← π.map_comp, ← c.map_comp]; rfl

def ov {Z : I} {p : ℕ} (i : ComposableArrows I p) (a : i.obj (Fin.last p) ⟶ Z) : ComposableArrows (Over Z) p :=
  mkO i (fun k => i.map (homOfLE (Fin.le_last k)) ≫ a) fun φ => by
    rw [← Category.assoc, ← i.map_comp]; rfl

theorem ov_eq {Z : I} {p : ℕ} (s : ComposableArrows (Over Z) p) : ov (s ⋙ Over.forget Z) (s.obj (Fin.last p)).hom = s := by
  have e : ∀ (a : ∀ k, (s ⋙ Over.forget Z).obj k ⟶ Z) h (e : a = fun k => (s.obj k).hom), mkO (s ⋙ Over.forget Z) a h = s := by
    intro a h e; subst e; rfl
  exact e _ _ (funext fun k => Over.w (s.map _))

def cmp {p q : ℕ} (f : Cn (relCn π F q) p) (c : ComposableArrows C q) :
    Cn ((Functor.const (Over (π.obj (c.obj 0)))).obj (F.obj (c.obj (Fin.last q)))) p :=
  fun s => f (s ⋙ Over.forget _) (st π c (s.obj (Fin.last p)).hom)

theorem cmp_inj {p q : ℕ} (f g : Cn (relCn π F q) p) (h : ∀ c, cmp π F f c = cmp π F g c) : f = g := by
  funext i x
  have key : ∀ f : Cn (relCn π F q) p, @Eq (F.obj (x.obj (Fin.last q)).right) (f i x)
      (cmp π F f (x ⋙ StructuredArrow.proj _ _) (ov i (x.obj 0).hom)) := fun f => by
    refine mkS_congr π F (f i) (x ⋙ StructuredArrow.proj _ _) (a := fun k => (x.obj k).hom)
      (a' := fun k => (i.map (𝟙 _) ≫ (x.obj 0).hom) ≫ π.map (x.map (homOfLE (Fin.zero_le k))).right)
      (st_w π (x ⋙ StructuredArrow.proj _ _) _) (funext fun k => ?_)
    rw [i.map_id, Category.id_comp]
    exact (StructuredArrow.w _).symm
  exact (key f).trans ((congrFun (h _) _).trans (key g).symm)

theorem cmp_surj {p q : ℕ} (g : ∀ c : ComposableArrows C q,
    Cn ((Functor.const (Over (π.obj (c.obj 0)))).obj (F.obj (c.obj (Fin.last q)))) p) :
    ∃ f : Cn (relCn π F q) p, ∀ c, cmp π F f c = g c := by
  refine ⟨fun i x => g (x ⋙ StructuredArrow.proj _ _) (ov i (x.obj 0).hom), fun c => funext fun s => ?_⟩
  change g c (ov (s ⋙ Over.forget _) ((s.obj (Fin.last p)).hom ≫ π.map (c.map (𝟙 0)))) = g c s
  rw [c.map_id, π.map_id, Category.comp_id, ov_eq]

theorem cmp_d {p q : ℕ} (f : Cn (relCn π F q) p) (c : ComposableArrows C q) :
    cmp π F (d _ p f) c = d _ p (cmp π F f c) := by
  funext s
  change (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (relRes π F (GlobalTheory.CatH.toLast k (s ⋙ Over.forget _))).pullC q
    (f (GlobalTheory.CatH.face k (s ⋙ Over.forget _)))) (st π c (s.obj (Fin.last (p + 1))).hom) =
    ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • cmp π F f c (GlobalTheory.CatH.face k s)
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => congrArg (fun z : F.obj (c.obj (Fin.last q)) => (-1 : ℤ) ^ (k : ℕ) • z) (a₁ := (relRes π F (GlobalTheory.CatH.toLast k (s ⋙ Over.forget _))).pullC q
    (f (GlobalTheory.CatH.face k (s ⋙ Over.forget _))) (st π c (s.obj (Fin.last (p + 1))).hom)) ?_
  refine mkS_congr π F (f (GlobalTheory.CatH.face k (s ⋙ Over.forget _))) c
    (a := fun l => (GlobalTheory.CatH.toLast k s).left ≫ (s.obj (Fin.last (p + 1))).hom ≫ π.map (c.map (homOfLE (Fin.zero_le l))))
    (a' := fun l => ((GlobalTheory.CatH.face k s).obj (Fin.last p)).hom ≫ π.map (c.map (homOfLE (Fin.zero_le l)))) (st_w π c _)
    (funext fun l => ?_)
  rw [← Category.assoc, Over.w]

theorem row_res (q : ℕ) : ((relCx π F).dcx.row q).ResUpTo 1 ((relAugRow π F).ε q) := by
  have T := fun c : ComposableArrows C q => terminal_res (R := R) _ (Over.mkIdTerminal (X := π.obj (c.obj 0))) (F.obj (c.obj (Fin.last q)))
  have he : ∀ (f : Cn F q) c, cmp π F ((relAugRow π F).ε q f) c = aug _ (fun _ => LinearMap.id) (f c) := fun f c => rfl
  refine ⟨(relAugRow π F).hε q, fun f hf => funext fun c => (T c).2.1 _ (by rw [← he, hf]; rfl), fun f hf => ?_, fun n f hf => ?_⟩
  · choose g hg using fun c => (T c).2.2.1 (cmp π F f c) (by
      change d _ 0 _ = 0
      rw [← cmp_d, show d (relCn π F q) 0 f = 0 from hf]; rfl)
    exact ⟨g, cmp_inj π F _ _ fun c => by rw [he, hg, one_smul, one_smul]⟩
  · choose g hg using fun c => (T c).2.2.2 n (cmp π F f c) (by
      change d _ (n + 1) _ = 0
      rw [← cmp_d, show d (relCn π F q) (n + 1) f = 0 from hf]; rfl)
    obtain ⟨g', hg'⟩ := cmp_surj π F g
    refine ⟨g', cmp_inj π F _ _ fun c => ?_⟩
    change cmp π F (d _ n g') c = _
    rw [cmp_d, hg', one_smul]
    exact (hg c).trans (one_smul _ _)

variable {C' : Type u'} [Category.{v'} C'] {F} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R))

def relHom : DCx.Hom (relCx π F).dcx (relCx (m.G ⋙ π) F').dcx (RingHom.id R) where
  f p q :=
    { toFun := fun g i => (relMor π m _).pullC q (g i)
      map_add' := fun g g' => funext fun i => map_add ((relMor π m _).pullC q) _ _
      map_smul' := fun r g => funext fun i => map_smul ((relMor π m _).pullC q) _ _ }
  ch p q g := by
    funext i
    change ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (relRes _ F' (GlobalTheory.CatH.toLast k i)).pullC q ((relMor π m _).pullC q (g (GlobalTheory.CatH.face k i))) =
      (relMor π m _).pullC q (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (relRes π F (GlobalTheory.CatH.toLast k i)).pullC q (g (GlobalTheory.CatH.face k i)))
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_zsmul]; rfl
  cv p q g := funext fun i => (relMor π m _).d_pullC q (g i)

theorem col_upTo (s : R) (p q : ℕ) (h : ∀ i, UpTo s ((relMor π m i).pull q)) : UpTo s (((relHom π m).col p).mapH q) := by
  constructor
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ q).1 x
    have ha' : ∀ i, d (relF π F _) q (a i) = 0 := fun i => congrFun ha i
    have hb := ((CrystallineSemistableComparison.P.cls_surj ((relCx (m.G ⋙ π) F').dcx.col p) q).2.1 (((relHom π m).col p).f q a)
      (by rw [Cx.Hom.comm, ha, map_zero])).1 hx
    have key : ∀ i, s • a i ∈ (cx (relF π F (i.obj (Fin.last p)))).B q := fun i => by
      refine ((CrystallineSemistableComparison.P.cls_surj (cx (relF π F _)) q).2.1 (s • a i) (by rw [map_smul]; exact (congrArg _ (ha' i)).trans (smul_zero _))).1 ?_
      refine (h _).1 ((cx (relF π F _)).cls (a i) (ha' i)) ?_
      refine ((CrystallineSemistableComparison.P.cls_surj (cx (relF (m.G ⋙ π) F' _)) q).2.1 ((relMor π m _).pullC q (a i))
        (by change d _ q _ = 0; rw [Mor.d_pullC, ha', map_zero])).2 ?_
      cases q with
      | zero => exact congrFun (show ((relHom π m).col p).f 0 a = 0 from hb) i
      | succ q => obtain ⟨y, hy⟩ := hb; exact ⟨y i, congrFun hy i⟩
    refine ((CrystallineSemistableComparison.P.cls_surj ((relCx π F).dcx.col p) q).2.1 (s • a) (by rw [map_smul, ha, smul_zero])).2 ?_
    cases q with
    | zero => exact funext fun i => key i
    | succ q => choose y hy using key; exact ⟨y, funext hy⟩
  · intro x
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ q).1 x
    have hb' : ∀ i, d (relF (m.G ⋙ π) F' _) q (b i) = 0 := fun i => congrFun hb i
    have key : ∀ i : ComposableArrows I p, ∃ a : Cn (relF π F (i.obj (Fin.last p))) q, d _ q a = 0 ∧
        (relMor π m _).pullC q a - (show Cn (relF (m.G ⋙ π) F' (i.obj (Fin.last p))) q from s • b i) ∈ (cx (relF (m.G ⋙ π) F' (i.obj (Fin.last p)))).B q := fun i => by
      obtain ⟨y, hy⟩ := (h _).2 ((cx (relF (m.G ⋙ π) F' _)).cls (b i) (hb' i))
      obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ q).1 y
      exact ⟨a, ha, ((CrystallineSemistableComparison.P.cls_surj (cx (relF (m.G ⋙ π) F' _)) q).2.2.1 _ (s • b i)
        (by change d _ q ((relMor π m _).pullC q a) = 0; rw [Mor.d_pullC, show d _ q a = 0 from ha, map_zero])
        (by rw [map_smul]; exact (congrArg _ (hb' i)).trans (smul_zero _))).1 hy⟩
    choose a ha hab using key
    refine ⟨((relCx π F).dcx.col p).cls a (funext ha), ?_⟩
    refine ((CrystallineSemistableComparison.P.cls_surj ((relCx (m.G ⋙ π) F').dcx.col p) q).2.2.1 (((relHom π m).col p).f q a) (s • b)
      (by rw [Cx.Hom.comm]; exact (congrArg _ (funext ha)).trans (map_zero _)) (by rw [map_smul, hb, smul_zero])).2 ?_
    cases q with
    | zero => exact funext fun i => hab i
    | succ q => choose y hy using hab; exact ⟨y, funext hy⟩

end CrystallineSemistableComparison.RelativeAugmentedComplex

open CrystallineSemistableComparison.RelativeAugmentedComplex in
theorem CrystallineSemistableComparison.P.rel : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {I : Type t} [Category.{t'} I] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (π : C ⥤ I) (m : Mor F F' (RingHom.id R)) (s : R) (n : ℕ), (∀ i, ∀ q ≤ n + 1, UpTo s ((relMor π m i).pull q)) → UpTo (s ^ (2 * n + 3)) (m.pull n) := by
  intro R _ C _ C' _ I _ F F' π m s n h
  have h1 := CrystallineSemistableComparison.P.dc_row (relAugRow π F) 1 (row_res π F) n
  have h2 := CrystallineSemistableComparison.P.dc_row (relAugRow (m.G ⋙ π) F') 1 (row_res _ F') n
  have h3 := CrystallineSemistableComparison.P.dc_map_col (relHom π m) s n fun p q hpq => col_upTo π m s p q fun i => h i q (by omega)
  rw [one_pow] at h1 h2
  have h4 := (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).1 h1 h3
  have e : (relHom π m).tot.mapH n ∘ₗ (relAugRow π F).edge.mapH n = (relAugRow (m.G ⋙ π) F').edge.mapH n ∘ₗ m.pull n := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 x
    refine congrArg Submodule.Quotient.mk (Subtype.ext (Subtype.ext (funext fun p => funext fun q => ?_)))
    change (relHom π m).f p q ((relCx π F).dcx.sgl 0 n ((relAugRow π F).ε n a) p q) =
      (relCx (m.G ⋙ π) F').dcx.sgl 0 n ((relAugRow (m.G ⋙ π) F').ε n (m.pullC n a)) p q
    by_cases hpq : p = 0 ∧ q = n
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [DCx.sgl_self, DCx.sgl_self]; rfl
    · rw [DCx.sgl_ne _ _ (by omega), DCx.sgl_ne _ _ (by omega), map_zero]
  rw [e] at h4
  have h5 := (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).2.2.1 h2 h4
  rwa [one_mul, one_mul] at h5
end
end
