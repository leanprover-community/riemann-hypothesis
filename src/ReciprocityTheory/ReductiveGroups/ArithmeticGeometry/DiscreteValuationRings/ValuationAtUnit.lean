import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.MemFinsetInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsAtScale
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.HrelPf

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem mem_pow_of_thick_zero' (G : Over (Spec (CommRingCat.of V))) [Flat G.hom] (ϖ : V) (hϖ : Irreducible ϖ)
    (U : G.left.Opens) (x : Γ(G.left, U)) (e : ℕ)
    (hx : ((fstG (maximalIdeal V) e G).left.app U).hom x = 0) :
    x ∈ Ideal.span {(G.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      ((G.hom.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ))} ^ (e + 1) := by
  obtain ⟨g, hg⟩ := exists_div G.hom (pow_ne_zero (e + 1) hϖ.ne_zero) U x fun y hy => by
    obtain ⟨W, hW, hyW, le₀⟩ := exists_isAffineOpen_mem_and_subset hy
    have le : W ≤ U := le₀
    let alg : V →+* Γ(G.left, W) :=
      (G.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
    have s₀ : hW.fromSpec ≫ G.hom = spMap alg := by
      rw [← IsAffineOpen.SpecMap_appLE_fromSpec G.hom (isAffineOpen_top _) hW (fun _ _ => trivial),
        IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl
    let J : Ideal Γ(G.left, W) := Ideal.span {alg (ϖ ^ (e + 1))}
    let q : V ⧸ maximalIdeal V ^ (e + 1) →+* Γ(G.left, W) ⧸ J := Ideal.quotientMap J alg (by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span rfl)
    have sq : (spMap (Ideal.Quotient.mk J) ≫ hW.fromSpec) ≫ G.hom = spMap q ≫ thick V (maximalIdeal V) e := by
      rw [Category.assoc, s₀, ← spMap_comp]
      exact (congrArg spMap (Ideal.quotientMap_comp_mk _).symm).trans (spMap_comp _ _)
    let r : Sp (Γ(G.left, W) ⧸ J) ⟶ (thickObj V (maximalIdeal V) e G).left := pullback.lift _ _ sq
    have r₁ : r ≫ fGl (maximalIdeal V) G e = spMap (Ideal.Quotient.mk J) ≫ hW.fromSpec := pullback.lift_fst _ _ _
    have z₀ : Ideal.Quotient.mk J ((G.left.presheaf.map (homOfLE le).op).hom x) = 0 := cst_ext fun z => by
      have hm : fGl (maximalIdeal V) G e (r z) ∈ U := (congrArg (fun m => m z ∈ U) r₁).mpr
        (le (hW.range_fromSpec.le ⟨spMap (Ideal.Quotient.mk J) z, rfl⟩))
      have e₁ := (gs_fromSpec hW le (spMap (Ideal.Quotient.mk J)) z x).trans (gs_spec _ z _)
      rw [← r₁] at e₁
      rw [← e₁, cst, map_zero, gs_zero _ z ⊤ trivial]
      exact (gs_pull r _ z U hm x).symm.trans ((congrArg (gs r z _) hx).trans (gs_zero r z _ hm))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 z₀)
    refine ⟨gs (𝟙 _) y W c, (gs_res (𝟙 _) y le hyW _).symm.trans ((congrArg (gs (𝟙 _) y W) hc).trans
      ((gs_mul _ y W hyW _ _).trans (congrArg₂ (· * ·) ?_ rfl)))⟩
    exact (gs_constFn G.hom W (𝟙 _) y hyW _).trans (by rw [Category.id_comp])
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hg, constFn, map_pow, map_pow]
  exact dvd_mul_right _ _

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem sec_zero_of_thick_zero' (hLB : lemmaBSt.{0}) (G : Over (Spec (CommRingCat.of V))) [GrpObj G]
    [hG : IsSemiAbelian G] (N : LB G.left) (hN : N.IsLB) (x : LB.Sec N)
    (hx : ∀ e i, ((fstG (maximalIdeal V) e G).left.app (N.U i)).hom (x.f i) = 0) : ∀ i, x.f i = 0 := by
  haveI := hG.comm
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI := hG.geomConnected
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine hLB V G N hN x ϖ hϖ fun i e => ?_
  rcases e with _ | e
  · simp
  · exact mem_pow_of_thick_zero' G ϖ hϖ _ _ e (hx e i)

set_option maxHeartbeats 1000000 in

theorem cross_global_of (hLaws : Laws) {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))} (P : Geo.Tor.PELUnif (maximalIdeal V) t)
    (a : NumberField.RingOfIntegers E) (N : ℕ)
    (hN : letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) (hN0 : 0 < N) {k : ℕ}
    (hCV : letI := H.starRing; ∀ (e : ℕ)
      (X : LB.Gen (LB.LinComb P.D.toPre.P.L ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left]
        ![((k * N : ℕ) : ℤ), -(k : ℤ)])), X.IsGen →
      ∀ (uR : LB.Gen (LB.LinComb P.D.toPre.P.L
        (rosatiφ P.D.toPre.P.A (P.oD.onB.act (star a)) (P.oD.onB.act a)) rosatiε)), uR.IsGen →
      LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ uR (zero2 P.D.toPre.P.A))
        (LB.oneGen P.D.toPre.P.L) →
      Function.Injective (fun χ : P.D.toPre.X => star a • χ) →
      ∀ (σ'' : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left)
          (fun _ => ((k * N : ℕ) : ℤ))))
        (τ : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))))
        (f'' : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α)
        (f : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB k α),
      (∀ i, P.U.ExpandsAt e (k * N) (σ'' i) (f'' i)) → (∀ i, P.U.ExpandsAt e k (τ i) (f i)) →
      (∀ i χ, ∃ u : LB.Gen (LB.LinComb P.D.toPre.P.L
          (Sum.elim (P.D.toPre.famφB (star a • χ)) (fun i => (P.oD.onB.act a).left ≫ P.D.toPre.famφB χ i))
          (pullε k N)),
        u.IsGen ∧
        LB.Gen.Corr P.D.toPre.P.L _ _ _ _ u (LB.mulGen P.D.toPre.P.L _ _ _ _ X
          (LB.pullGen P.D.toPre.P.L _ _ uR (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c χ) (𝟙 P.D.toPre.P.A)).left)) ∧
        GeneratorPullback.SecRel P.D.toPre.P.L (P.D.toPre.famφB (star a • χ)) (DegPre.famε (k * N))
          (f'' i (star a • χ)) (P.D.toPre.famφB χ) (DegPre.famε k) (f i χ) (P.oD.onB.act a).left
          (Sum.elim (P.D.toPre.famφB (star a • χ)) (fun i => (P.oD.onB.act a).left ≫ P.D.toPre.famφB χ i))
          (pullε k N) u) →
      (∀ i β, (∀ χ, β ≠ star a • χ) → ∀ j, (f'' i β).f j = 0) →
      ∀ j, ((fstG (maximalIdeal V) e t.G).left.app _).hom
        ((mulSec P.U.LG.L _ _ _ _ (σ'' 0) (pullSec P.U.LG.L _ _ (τ 1) (t.act.act a).left)).f j -
          (mulSec P.U.LG.L _ _ _ _ (σ'' 1) (pullSec P.U.LG.L _ _ (τ 0) (t.act.act a).left)).f j) = 0)
    (s : Fin 2 → P.U.SecK k) (F : Fin 2 → Fam P.D.toPre (FractionRing V) k) (hs : ∀ i, P.U.Expands k (s i) (F i))
    (s'' : Fin 2 → P.U.SecK (k * N)) (F'' : Fin 2 → Fam P.D.toPre (FractionRing V) (k * N))
    (hs'' : ∀ i, P.U.Expands (k * N) (s'' i) (F'' i))
    (hPA : letI := H.starRing; ∀ i, PullAl P.D (FractionRing V) P.oD a k N (F i) (F'' i)) :
    ∀ j, (mulSec P.U.LG.L _ _ _ _ (s'' 0) (pullSec P.U.LG.L _ _ (s 1) (endK (t.act.act a)))).f j =
      (mulSec P.U.LG.L _ _ _ _ (s'' 1) (pullSec P.U.LG.L _ _ (s 0) (endK (t.act.act a)))).f j := by
  letI := H.starRing
  have hL : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  choose r hr σ f hsσ hsf hexp using hs
  choose r'' hr'' σ'' f'' hsσ'' hsf'' hexp'' using hs''
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  obtain ⟨X, hX, hXn⟩ := exists_XB P.D hL P.oD H.w0 uΨ huΨ a N hN hN0 k
  obtain ⟨uR, huR, huR0⟩ := exists_uR P.D P.oD a

  let σn : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((k * N : ℕ) : ℤ))) :=
    fun i => SecOps.secScale (scal t.G.hom (r i)) (σ'' i)
  let f''n : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α :=
    fun i α => SecOps.secScale (scal P.D.toPre.P.A.hom (r i)) (f'' i α)
  let τn : Fin 2 → LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))) :=
    fun i => SecOps.secScale (scal t.G.hom (r'' i)) (σ i)
  let fn : Fin 2 → ∀ α : P.D.toPre.X, P.D.toPre.SecB k α :=
    fun i α => SecOps.secScale (scal P.D.toPre.P.A.hom (r'' i)) (f i α)
  have hprB : (DegPre.prB P.D.toPre (FractionRing V)).left ≫ P.D.toPre.P.A.hom =
      (DegPre.BF P.D.toPre (FractionRing V)).hom := Over.w _
  have hgK : pullback.fst t.G.hom (jK V) ≫ t.G.hom = pullback.snd t.G.hom (jK V) ≫ jK V := pullback.condition
  have hfn : ∀ i α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε k)
      ((F i).s α) (P.D.toPre.famφB α) (DegPre.famε k) (fn i α) (DegPre.prB P.D.toPre (FractionRing V)).left
      (scal (DegPre.BF P.D.toPre (FractionRing V)).hom (r i * r'' i)) := fun i α => by
    have := secScal_scale (hsf i α) (scal P.D.toPre.P.A.hom (r'' i))
    rwa [scal_pull _ _ _ hprB, ← scal_mul, mul_comm] at this
  have hf''n : ∀ i α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε (k * N))
      ((F'' i).s α) (P.D.toPre.famφB α) (DegPre.famε (k * N)) (f''n i α) (DegPre.prB P.D.toPre (FractionRing V)).left
      (scal (DegPre.BF P.D.toPre (FractionRing V)).hom (r i * r'' i)) := fun i α => by
    have := secScal_scale (hsf'' i α) (scal P.D.toPre.P.A.hom (r i))
    rwa [scal_pull _ _ _ hprB, ← scal_mul] at this
  have hσn : ∀ i, GeneratorPullback.SecScal P.U.LG.L (fun _ : Fin 1 => pullback.fst t.G.hom (jK V)) (fun _ => ((k * N : ℕ) : ℤ))
      (s'' i) (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => ((k * N : ℕ) : ℤ)) (σn i) (pullback.fst t.G.hom (jK V))
      (scal (pullback.snd t.G.hom (jK V) ≫ jK V) (r i * r'' i)) := fun i => by
    have := secScal_scale (hsσ'' i) (scal t.G.hom (r i))
    rwa [scal_pull _ _ _ hgK, ← scal_mul] at this
  have hτn : ∀ i, GeneratorPullback.SecScal P.U.LG.L (fun _ : Fin 1 => pullback.fst t.G.hom (jK V)) (fun _ => (k : ℤ))
      (s i) (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => (k : ℤ)) (τn i) (pullback.fst t.G.hom (jK V))
      (scal (pullback.snd t.G.hom (jK V) ≫ jK V) (r i * r'' i)) := fun i => by
    have := secScal_scale (hsσ i) (scal t.G.hom (r'' i))
    rwa [scal_pull _ _ _ hgK, ← scal_mul, mul_comm] at this
  have hrel := fun i => hrel_integral_pf P.D hLaws.globalFns P.oD a N hN hN0 k X hX hXn uR huR huR0 (F i) (F'' i)
    (hPA i) (r i * r'' i) (fn i) (f''n i) (hfn i) (hf''n i)
  have hinj : Function.Injective (fun χ : P.D.toPre.X => star a • χ) :=
    fun _ _ h => smul_star_inj a N hN hN0 h
  have hexpn'' : ∀ e i, P.U.ExpandsAt e (k * N) (σn i) (f''n i) := fun e i =>
    expandsAt_scale P.U.toUnifPre e (k * N) (σ'' i) (f'' i) (r i) (hexp'' i e)
  have hexpn : ∀ e i, P.U.ExpandsAt e k (τn i) (fn i) := fun e i =>
    expandsAt_scale P.U.toUnifPre e k (σ i) (f i) (r'' i) (hexp i e)
  have hv := fun e => hCV e X hX uR huR huR0 hinj σn τn f''n fn (hexpn'' e) (hexpn e)
    (fun i χ => (hrel i).1 χ) (fun i => (hrel i).2)

  let C := SecOps.secAdd (mulSec P.U.LG.L _ _ _ _ (σn 0) (pullSec P.U.LG.L _ _ (τn 1) (t.act.act a).left))
    (SecOps.secNeg (mulSec P.U.LG.L _ _ _ _ (σn 1) (pullSec P.U.LG.L _ _ (τn 0) (t.act.act a).left)))
  haveI := t.semi
  have hC0 := sec_zero_of_thick_zero' hLaws.lemmaB t.G _ (linComb_isLB P.U.LG.L P.U.LG.isLB _ _) C
    (fun e j => by
      have := hv e j
      simpa [C, SecOps.secAdd, SecOps.secNeg, sub_eq_add_neg] using this)
  have hrK : ∀ i, r i * r'' i ≠ 0 := fun i => mul_ne_zero (hr i) (hr'' i)
  refine cross_to_K P.U.LG.L P.U.LG.isLB (t.act.act a) k (k * N) σn τn s'' s (fun i => r i * r'' i) hrK hσn hτn ?_
  intro j
  have := hC0 j
  simp only [C, SecOps.secAdd, SecOps.secNeg] at this
  exact (add_neg_eq_zero).1 this

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem cross_global (hLaws : Laws) (hL4 : Laws4) {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))} (P : Geo.Tor.PELUnif (maximalIdeal V) t)
    (a : NumberField.RingOfIntegers E) (N : ℕ)
    (hN : letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) (hN0 : 0 < N) {k : ℕ} (hk : 1 ≤ k)
    (s : Fin 2 → P.U.SecK k) (F : Fin 2 → Fam P.D.toPre (FractionRing V) k) (hs : ∀ i, P.U.Expands k (s i) (F i))
    (s'' : Fin 2 → P.U.SecK (k * N)) (F'' : Fin 2 → Fam P.D.toPre (FractionRing V) (k * N))
    (hs'' : ∀ i, P.U.Expands (k * N) (s'' i) (F'' i))
    (hPA : letI := H.starRing; ∀ i, PullAl P.D (FractionRing V) P.oD a k N (F i) (F'' i)) :
    ∀ j, (mulSec P.U.LG.L _ _ _ _ (s'' 0) (pullSec P.U.LG.L _ _ (s 1) (endK (t.act.act a)))).f j =
      (mulSec P.U.LG.L _ _ _ _ (s'' 1) (pullSec P.U.LG.L _ _ (s 0) (endK (t.act.act a)))).f j := by
  letI := H.starRing
  exact cross_global_of hLaws P a N hN hN0
    (fun e X hX uR huR huR0 hinj σ'' τ f'' f h'' hf hrel hoff =>
      cross_vanish hL4 P a k N e X hX uR huR huR0 hinj σ'' τ f'' f h'' hf hrel hoff)
    s F hs s'' F'' hs'' hPA

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.ValuationAtUnit

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

def ValAtUnit {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))}
    (P : Geo.Tor.PELUnif (maximalIdeal V) t) (k : ℕ) (s : P.U.SecK k) (x : FractionRing V) : Prop :=
  ∃ τ : LB.Gen (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => unitK ≫ gK) (fun _ => (k : ℤ))), τ.IsGen ∧
    LB.Gen.Corr P.U.LG.L _ _ _ _ τ
      (LB.pullGen P.U.LG.L _ _ (GeneratorPullback.powGen P.U.LG.L _ _ P.U.LG.rig k) (jK V)) ∧
    ∀ j, rs (wchart_comp_le (L := P.U.LG.L) (fun _ : Fin 1 => gK) unitK j) ((unitK.app _).hom (s.f j)) =
      ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE le_top).op).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom x) * (τ.s j).val

theorem eq_of_gs_eq {F : Type} [Field F] (z : Spec (CommRingCat.of F)) (c c' : F)
    (h : gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c')) : c = c' := by
  have hz : (𝟙 (Spec (CommRingCat.of F)) : _) z ∈ (⊤ : (Spec (CommRingCat.of F)).Opens) := trivial
  unfold gs at h
  rw [dif_pos hz, dif_pos hz] at h
  have h2 : (Scheme.Hom.app (𝟙 (Spec (CommRingCat.of F))) ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) =
      (Scheme.Hom.app (𝟙 (Spec (CommRingCat.of F))) ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c') := by
    first
    | exact AlgebraicGeometry.germ_injective_of_isIntegral _ _ hz h
    | exact AlgebraicGeometry.germ_injective_of_isIntegral _ _ _ hz h
    | exact AlgebraicGeometry.germ_injective_of_isIntegral _ hz h
    | exact AlgebraicGeometry.germ_injective_of_isIntegral (Spec (CommRingCat.of F)) h
  have h2' : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c = (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c' := by
    first
    | exact h2
    | simpa only [RingHom.id_apply] using h2
    | (simp only [Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply] at h2; exact h2)
  have h3 := congrArg (fun y => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom y) h2'
  simpa using h3

theorem valueAtZero_unique_of_stalk_reading {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ}
    {α : D.toPre.X} {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {c c' : F}
    (h : Val0 D F k α s c) (h' : Val0 D F k α s c') : c = c' := by
  obtain ⟨τ, -, cτ, eτ⟩ := h
  obtain ⟨τ', -, cτ', eτ'⟩ := h'
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  choose J hJ using fun χ : Spec (CommRingCat.of F) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ z)
  have hm := Good.mem hJ (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) (𝟙 _)
  have e := congrArg (gs (𝟙 _) z _)
    ((eτ (fun i => J (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i))).symm.trans
      (eτ' (fun i => J (𝟙 _ ≫ (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i))))
  have A := (gs_mul (𝟙 _) z _ hm _ _).symm.trans (e.trans (gs_mul (𝟙 _) z _ hm _ _))
  let r0 : Spec (CommRingCat.of F) ⟶ (TF (R := V) F).left := 𝟙 _
  have B : gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) *
        (val τ r0 z J).val =
      gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c') *
        (val τ' r0 z J).val := by
    convert A using 2 <;> first
      | exact (gs_res (𝟙 _) z le_top hm _).symm
      | exact (gs_unit (𝟙 _) z _ hm _).symm
  rw [val_corr hJ cτ, val_corr hJ cτ'] at B
  exact eq_of_gs_eq z c c' (mul_right_cancel₀ (Units.ne_zero _) B)


theorem exists_glue_ratio {Y : Scheme.{0}} {M : LB Y} (hc : ⨆ j, M.U j = ⊤) (s : LB.Sec M) (τ : LB.Gen M)
    (hτ : τ.IsGen) : ∃ a : Γ(Y, ⊤), ∀ j, s.f j = (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a * (τ.s j).val := by
  let r : ∀ j, Γ(Y, M.U j) := fun j => s.f j * ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val
  have compat : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom (r i) =
      (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (r j) := by
    intro i j
    have hs := s.compat i j
    have hti : (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom ((τ.s i)⁻¹ : Γ(Y, M.U i)ˣ).val =
        (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val *
          ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val := by
      have := congrArg (fun u => (u⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val) (hτ i j)
      simp only [mul_inv_rev, Units.val_mul] at this
      exact this
    have hg : (M.g i j : Γ(Y, M.U i ⊓ M.U j)ˣ).val * ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val = 1 := by
      rw [← Units.val_mul, _root_.mul_inv_cancel, Units.val_one]
    simp only [r, map_mul]
    rw [hs, hti]
    linear_combination ((Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (s.f j) *
      (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val) * hg
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hc.ge r compat
  have ha' : ∀ j, (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a = r j := ha
  refine ⟨a, fun j => ?_⟩
  rw [ha' j]
  simp only [r]
  rw [_root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.mul_one]


end ReciprocityTheory.ChartRestriction.G.DVR.ValuationAtUnit
end
end
