import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticePrismaticFCrystalPerfectPrism
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfEquivariantEtaleMapAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.Prism.ModelChange

def Via {B C : Type} [CommRing B] [CommRing C] (_g : B →+* C) (Q : Type) : Type := Q

instance instAddCommGroupVia {B C : Type} [CommRing B] [CommRing C] (g : B →+* C) (Q : Type)
    [AddCommGroup Q] : AddCommGroup (Via g Q) := ‹AddCommGroup Q›

instance instModuleVia {B C : Type} [CommRing B] [CommRing C] (g : B →+* C) (Q : Type) [AddCommGroup Q]
    [Module C Q] : Module B (Via g Q) := Module.compHom Q g

theorem semiBC_comp {A B C M N P : Type} [CommRing A] [CommRing B] [CommRing C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P]
    {f : A →+* B} {g : B →+* C} {h : A →+* C} (hfg : ∀ a, g (f a) = h a)
    {u : M →ₛₗ[f] N} {v : N →ₛₗ[g] P} {w : M →ₛₗ[h] P} (hw : ∀ x, w x = v (u x))
    (hu : SemiBC u) (hv : SemiBC v) : SemiBC w := by
  intro Q _ _ q
  let q₁ : M →ₛₗ[f] Via g Q :=
    { toFun := fun x => (q x : Q)
      map_add' := fun x y => map_add q x y
      map_smul' := fun a x => by
        change q (a • x) = g (f a) • (q x : Q)
        rw [q.map_smulₛₗ, hfg] }
  obtain ⟨w₁, hw₁, hu₁⟩ := hu (Via g Q) q₁
  let w₂ : N →ₛₗ[g] Q :=
    { toFun := fun y => (w₁ y : Q)
      map_add' := fun y z => map_add w₁ y z
      map_smul' := fun b y => w₁.map_smul b y }
  obtain ⟨w₃, hw₃, hu₃⟩ := hv Q w₂
  refine ⟨w₃, fun x => ?_, fun w' hw' => ?_⟩
  · rw [hw, hw₃]; exact hw₁ x
  · let w'' : N →ₗ[B] Via g Q :=
      { toFun := fun y => (w' (v y) : Q)
        map_add' := fun y z => by
          change w' (v (y + z)) = w' (v y) + w' (v z)
          rw [map_add, map_add]
        map_smul' := fun b y => by
          change w' (v (b • y)) = g b • w' (v y)
          rw [v.map_smulₛₗ, w'.map_smul] }
    have h1 : w'' = w₁ := hu₁ w'' fun x => by
      change w' (v (u x)) = q x
      rw [← hw x]; exact hw' x
    exact hu₃ w' fun y => by
      change w' (v y) = (w₁ y : Q)
      rw [← h1]; rfl

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem torsionFree_of_equiv {P : Obj l ↥(OL K)} (e : P.A ≃+* Ainf l) (x : P.A) (h : (l : P.A) * x = 0) :
    x = 0 :=
  e.injective (by rw [map_zero]; apply ainf_torsionFree; rw [← map_natCast e, ← map_mul, h, map_zero])

def toAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) : Hom P (ainfObj K) where
  f := e.toRingHom
  f_δ := P.D.map_δ_of_map_φ (ainfObj K).D ainf_torsionFree _ fun a => H.e_φ a
  f_I a ha := ((isAinf_ainfObj K).e_I (e a)).2 ((H.e_I a).1 ha)
  f_str r a h := ((isAinf_ainfObj K).mk_eq_str_iff r (e a)).2 ((H.mk_eq_str_iff r a).1 h)

def ofAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) : Hom (ainfObj K) P where
  f := e.symm.toRingHom
  f_δ := (ainfObj K).D.map_δ_of_map_φ P.D (torsionFree_of_equiv e) _ fun a => e.injective
      ((e.apply_symm_apply _).trans ((congrArg WittVector.frobenius (e.apply_symm_apply (a : Ainf l))).symm.trans
        (H.e_φ _).symm))
  f_I a ha := (H.e_I _).2
      ((congrArg (Per.θ l) (e.apply_symm_apply (a : Ainf l))).trans (((isAinf_ainfObj K).e_I a).1 ha))
  f_str r a h := (H.mk_eq_str_iff r _).2
      ((congrArg (Per.θ l) (e.apply_symm_apply (a : Ainf l))).trans (((isAinf_ainfObj K).mk_eq_str_iff r a).1 h))

theorem ofAinf_comp_toAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) :
    (ofAinf H).comp (toAinf H) = Hom.id P :=
  Hom.ext' (RingHom.ext fun a => e.symm_apply_apply a)

theorem toAinf_comp_ofAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) :
    (toAinf H).comp (ofAinf H) = Hom.id (ainfObj K) :=
  Hom.ext' (RingHom.ext fun a => e.apply_symm_apply a)

variable {T : Type} [AddCommGroup T] [Module ℤ_[l] T]

def jOfModel {M : FCrys l ↥(OL K)} {P P' : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} {e' : P'.A ≃+* Ainf l}
    (c : Hom P P') (hc : ∀ a, e' (c.f a) = e a)
    (j' : M.M P' →ₛₗ[(inclW l).comp e'.toRingHom] (WCb l ⊗[ℤ_[l]] T)) :
    M.M P →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T) where
  toFun x := j' (M.tr c x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' a x := by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
    change inclW l (e' (c.f a)) • _ = inclW l (e a) • _
    rw [hc]

theorem realises_of {M : FCrys l ↥(OL K)} {P P' : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l}
    {e' : P'.A ≃+* Ainf l} {ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)} (H : IsAinf K P e) (c : Hom P P')
    (hc : ∀ a, e' (c.f a) = e a) {j' : M.M P' →ₛₗ[(inclW l).comp e'.toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (hj : Realises K M P' e' T ρ j') : Realises K M P e T ρ (jOfModel c hc j') := by
  have H' := hj.ainf
  obtain ⟨d₀, hd, hd0⟩ := H.exists_generator
  refine Realises.of_generator H ?_ d₀ hd ?_ ?_
  · exact semiBC_comp (f := c.f) (g := (inclW l).comp e'.toRingHom) (h := (inclW l).comp e.toRingHom)
      (u := M.tr c) (v := j') (w := jOfModel c hc j') (fun a => congrArg (inclW l) (hc a)) (fun _ => rfl)
      (M.tr_bc c) hj.bc
  · intro x m k h
    have : IsDomain P'.A := e'.toMulEquiv.isDomain
    have := M.proj P'
    let d' : ↥P'.I := ⟨c.f d₀, c.f_I _ d₀.2⟩
    have hd'e : e' (d' : P'.A) = e d₀ := hc _
    have hd'0 : (d' : P'.A) ≠ 0 := fun h0 => hd0 (e.injective (by rw [← hd'e, h0, map_zero, map_zero]))
    obtain ⟨n, i, hn⟩ := exists_isFrac (d' : P'.A) (M.Φ P' d' (M.tr c x))
    obtain ⟨r, hr⟩ := M.Φ_nat c d₀ d' x m k n i h hn
    have heq : (d' : P'.A) ^ i • M.tr c m = (d' : P'.A) ^ k • n :=
      sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ (mul_ne_zero hd'0 hd'0)))
    have hu : IsUnit (((inclW l).comp e'.toRingHom) (d' : P'.A)) := by
      change IsUnit (inclW l (e' (d' : P'.A))); rw [hd'e]; exact H.isUnit_inclW hd
    have key := smul_eq_of_isUnit j' hu heq (hj.j_φ d' hd'0 (M.tr c x) n i hn)
    change inclW l (e d₀) ^ k • _ = j' (M.tr c m)
    rw [← hd'e]; exact key
  · intro g x
    have hcg : c.comp (H.galHom g) = (H'.galHom g).comp c := Hom.ext' (RingHom.ext fun a => e'.injective (by
      change e' (c.f ((H.galHom g).f a)) = e' ((H'.galHom g).f (c.f a))
      rw [hc, H.e_galHom, H'.e_galHom, hc]))
    have e0 : M.tr c (M.tr (H.galHom g) x) = M.tr (H'.galHom g) (M.tr c x) :=
      (M.tr_comp _ _ x).symm.trans ((congrArg (fun f => M.tr f x) hcg).trans (M.tr_comp _ _ x))
    exact (congrArg j' e0).trans (hj.j_act g (M.tr c x))

end GlobalTheory.Prism.ModelChange

open GlobalTheory.Prism.ModelChange in

theorem GlobalTheory.Prism.realisation_indep_model : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e₀ : P₀.A ≃+* Ainf l), IsAinf K P₀ e₀ → ∃ a : Hom P₀ (ainfObj K), ∀ (M : FCrys l ↥(OL K)), Function.Bijective (M.tr a) ∧ ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)), (∀ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ → ∃ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j) ∧ (∀ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j → ∃ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ ∧ ∀ x, j₀ (M.tr a x) = j x) := by
  intro l _ K P₀ e₀ H
  refine ⟨toAinf H, fun M => ⟨?_, fun T _ _ ρ => ⟨fun j₀ hj₀ => ⟨_, realises_of H (toAinf H) (fun _ => rfl) hj₀⟩,
    fun j hj => ⟨_, realises_of (isAinf_ainfObj K) (ofAinf H) (fun a => by exact e₀.apply_symm_apply a) hj,
      fun x => ?_⟩⟩⟩⟩
  · refine Function.bijective_iff_has_inverse.2 ⟨M.tr (ofAinf H), fun x => ?_, fun y => ?_⟩
    · rw [← M.tr_comp, ofAinf_comp_toAinf, M.tr_id]
    · rw [← M.tr_comp, toAinf_comp_ofAinf, M.tr_id]
  · change j (M.tr (ofAinf H) (M.tr (toAinf H) x)) = j x
    rw [← M.tr_comp, ofAinf_comp_toAinf, M.tr_id]
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleRealisation_indep_ainfModel : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e₀ : P₀.A ≃+* Ainf l), IsAinf K P₀ e₀ → ∃ a : Hom P₀ (ainfObj K), ∀ (M : FCrys l ↥(OL K)), Function.Bijective (M.tr a) ∧ ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)), (∀ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ → ∃ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j) ∧ (∀ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j → ∃ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ ∧ ∀ x, j₀ (M.tr a x) = j x) := by
  atlas_forward_decl GlobalTheory.Prism.realisation_indep_model
end

section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semiBC_injective_of_injective : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B),
    Function.Injective f → ∀ (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N),
    SemiBC u → Function.Injective u := by
  intro A B _ _ f hf M _ _ _ _ N _ _ u h
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let v : M →ₛₗ[f] (Fin n → B) :=
    { toFun := fun x i => f (s x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  rw [← LinearMap.ker_eq_bot (τ₁₂ := f), LinearMap.ker_eq_bot']
  intro x hx
  have h1 : v x = 0 := by rw [← hS, hx, map_zero]
  have h2 : s x = 0 := by
    funext i
    apply hf
    rw [Pi.zero_apply, map_zero]
    exact congrFun h1 i
  have h3 : x = p (s x) := by
    rw [← LinearMap.comp_apply, hps, LinearMap.id_apply]
  rw [h3, h2, map_zero]

end GlobalTheory.BSP
end
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} {R : Type} [CommRing R]

theorem FHom.ext_u {M M' : FCrys l R} {u u' : FHom M M'} (h : ∀ P, u.u P = u'.u P) : u = u' := by
  cases u; cases u'
  congr
  funext P
  exact h P

theorem FHom.eq_of_tr {M M' : FCrys l R} (u u' : FHom M M') {P Q : Obj l R} (g : Hom P Q)
    (hP : u.u P = u'.u P) : u.u Q = u'.u Q := by
  let v : M.M P →ₛₗ[g.f] M'.M Q := (M'.tr g).comp (u.u P)
  obtain ⟨w, -, hw⟩ := M.tr_bc g (M'.M Q) v
  have h1 := hw (u.u Q) fun x => by simp [v, u.u_tr]
  have h2 := hw (u'.u Q) fun x => by simp [v, u'.u_tr, hP]
  rw [h1, h2]

theorem FHom.eq_of_inj {M M' : FCrys l R} (u u' : FHom M M') {B C : Obj l R} (h : Hom B C)
    (hinj : Function.Injective h.f) (hC : u.u C = u'.u C) : u.u B = u'.u B := by
  haveI := M'.fin B
  haveI := M'.proj B
  have hi : Function.Injective (M'.tr h) :=
    semiBC_injective_of_injective _ _ h.f hinj _ _ (M'.tr h) (M'.tr_bc h)
  ext x
  apply hi
  rw [← u.u_tr, ← u'.u_tr, hC]

theorem fhom_ext_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M M' : FCrys l ↥(OL K))
    (u u' : FHom M M'), u.u bk.prism = u'.u bk.prism → u = u' := by
  intro l _ K bk M M' u u' hbk
  apply FHom.ext_u
  intro B
  obtain ⟨C, h, ⟨g⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  have hC := FHom.eq_of_tr u u' g hbk
  exact FHom.eq_of_inj u u' h (GlobalTheory.T.prism_cover_injective_and_descent l _ B C h hc).1 hC

end GlobalTheory.BSP
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticFCrystalHom_ext_breuilKisin_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M M' : FCrys l ↥(OL K)) (u u' : FHom M M'), u.u bk.prism = u'.u bk.prism → u = u' := by
  atlas_forward_decl GlobalTheory.BSP.fhom_ext_bk
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bk_ev_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Function.Injective bk.ev := by
  intro l _ K bk
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  intro a a' h
  have h1 : tb.c tb.i₀ 1 = 1 := by simpa [tb.b_i₀] using tb.c_self tb.i₀
  have key : ∀ x, tb.c tb.i₀ (bk.ev x) = x := fun x => by
    have := tb.c_mul tb.i₀ x (tb.b tb.i₀)
    rw [tb.b_i₀, mul_one, h1, mul_one] at this
    exact this
  rw [← key a, ← key a', h]

end GlobalTheory.BSP
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinDatum_structureMap_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Function.Injective bk.ev := by
  atlas_forward_decl GlobalTheory.BSP.bk_ev_injective
end

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem fHom_eq_of_realises : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T']
    (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K))
    (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')),
    Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ u u' : FHom M M',
      (∀ x, j' (u.u (ainfObj K) x) = j' (u'.u (ainfObj K) x)) → u = u' := by
  intro l _ K T' _ _ ρ' M M' j' H u u' h
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  apply GlobalTheory.T.prismaticFCrystalHom_ext_breuilKisin_prism l K bk M M' u u'
  haveI := M'.fin (ainfObj K)
  haveI := M'.proj (ainfObj K)
  haveI := M'.fin bk.prism
  haveI := M'.proj bk.prism
  have hj : Function.Injective j' :=
    semiBC_injective_of_injective _ _ ((inclW l).comp (ainfId K).toRingHom)
      (GlobalTheory.Prism.inclW_injective.comp (ainfId K).injective) _ _ j' H.bc
  have ht : Function.Injective (M'.tr bk.ι) :=
    semiBC_injective_of_injective _ _ bk.ι.f (GlobalTheory.T.breuilKisinDatum_structureMap_injective l K bk) _ _ (M'.tr bk.ι) (M'.tr_bc bk.ι)
  refine LinearMap.ext fun x => ht (hj ?_)
  rw [← u.u_tr, ← u'.u_tr]
  exact h _

end GlobalTheory.BSP
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fCrystalHom_eq_of_etale_realisation_perfectPrism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T'] (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K)) (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')), Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ u u' : FHom M M', (∀ x, j' (u.u (ainfObj K) x) = j' (u'.u (ainfObj K) x)) → u = u' := by
  atlas_forward_decl GlobalTheory.BSP.fHom_eq_of_realises
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bhattScholzeIntegral : GlobalTheory.Published.BhattScholzeIntegral := by
  intro l _ K P₀ e H
  obtain ⟨a, ha⟩ := GlobalTheory.T.etaleRealisation_indep_ainfModel l K P₀ e H
  refine ⟨?_, ?_⟩
  · intro P AI hstd V _ _ _ _ _ _ _ ρ L hc hcr
    obtain ⟨M, j₀, hj₀⟩ := GlobalTheory.T.crystallineLattice_prismaticFCrystal_perfectPrism l K P AI hstd V ρ L hc hcr
    obtain ⟨j, hj⟩ := ((ha M).2 ↥L.T (fun g => actT L g)).1 j₀ hj₀
    exact ⟨M, j, hj⟩
  · intro T T' _ _ _ _ ρ ρ' E E' j j' hj hj' f hf
    obtain ⟨j₀, hj₀, e₀⟩ := ((ha E).2 T ρ).2 j hj
    obtain ⟨j₀', hj₀', e₀'⟩ := ((ha E').2 T' ρ').2 j' hj'
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_FCrystalHom_of_equivariantEtaleMap_ainf l K T ρ T' ρ' E E' j₀ j₀' hj₀ hj₀' f hf
    refine ⟨u, fun x => ?_, fun u' hu' => ?_⟩
    · exact (e₀' _).symm.trans ((congrArg j₀' (u.u_tr a x).symm).trans
        ((hu _).trans (congrArg (f.lTensor (WCb l)) (e₀ x))))
    · refine GlobalTheory.T.fCrystalHom_eq_of_etale_realisation_perfectPrism l K T' ρ' E E' j₀' hj₀' u' u fun y => ?_
      obtain ⟨x, rfl⟩ := (ha E).1.2 y
      exact (congrArg j₀' (u'.u_tr a x)).trans ((e₀' _).trans ((hu' x).trans
        ((congrArg (f.lTensor (WCb l)) (e₀ x).symm).trans (hu _).symm)))

end GlobalTheory.BSP
end
