import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjBCompl
import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemBasicOpenSecHomIff
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FromSpecResidueFieldAppTopIso
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehom

section
namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

variable {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}

theorem val_eval₂ {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) [LocallyOfFiniteType s] {U : S.Opens}
    {σ : Type} (u : σ → Γ(S, U)) (F : MvPolynomial σ ℂ) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) :
    val s (eval₂ (constSec s U) u F) x hx = eval (fun t => val s (u t) x hx) F := by
  obtain ⟨φ, hφ⟩ := val_ringHom s U x hx hc
  rw [← hφ, eval₂_comp_left]
  have h1 : φ.comp (constSec s U) = RingHom.id ℂ := by
    ext c
    simp only [RingHom.comp_apply, hφ, RingHom.id_apply]
    exact val_const s U x hx hc c
  rw [h1]
  change eval₂ (RingHom.id ℂ) (φ ∘ u) F = eval₂ (RingHom.id ℂ) _ F
  congr 1
  funext t
  exact hφ (u t)

namespace AffPres

set_option backward.isDefEq.respectTransparency false in

theorem secHom_C (P : AffPres sW) (c : ℂ) : P.secHom (C c) = constSec sW P.V c := by
  have key : (Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sW.appLE ⊤ P.V le_top := by
    rw [← Scheme.Hom.comp_appTop_assoc, P.hover, Scheme.Hom.comp_appTop, Category.assoc]
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE, Scheme.Opens.ι_appTop,
      Scheme.Opens.topIso_hom, ← W.presheaf.map_comp]
    rfl
  have e3 : P.secHom (C c) = ((CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K))) ≫
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom) c := rfl
  rw [e3, Scheme.ΓSpecIso_inv_naturality_assoc, key]
  rfl

theorem secHom_surjective (P : AffPres sW) : Function.Surjective P.secHom := by
  intro a
  have h1 : Function.Surjective P.V.topIso.hom.hom :=
    (ConcreteCategory.bijective_of_isIso P.V.topIso.hom).2
  have h2 : Function.Surjective (P.iso.hom.app ⊤).hom :=
    (ConcreteCategory.bijective_of_isIso (P.iso.hom.app ⊤)).2
  have h3 : Function.Surjective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2
  obtain ⟨a1, rfl⟩ := h1 a
  obtain ⟨a2, rfl⟩ := h2 a1
  obtain ⟨a3, rfl⟩ := h3 a2
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a3
  exact ⟨f, rfl⟩

theorem val_secHom [LocallyOfFiniteType sW] (P : AffPres sW) (y : W) (hy : y ∈ P.V)
    (hc : IsClosed ({y} : Set W)) (f : MvPolynomial (Fin P.n) ℂ) :
    val sW (P.secHom f) y hy = eval (P.coord y hy) f := by
  obtain ⟨φ, hφ⟩ := val_ringHom sW P.V y hy hc
  have hker : ∀ g ∈ ptIdeal (P.coord y hy), val sW (P.secHom g) y hy = 0 := by
    intro g hg
    rw [val_eq_zero_iff sW _ y hy hc, ← Scheme.germ_residue, CommRingCat.comp_apply]
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    have h2 : P.stalkEquiv y hy hc (W.presheaf.germ P.V y hy (P.secHom g)) ∈
        (IsLocalRing.maximalIdeal (W.presheaf.stalk y)).map (P.stalkEquiv y hy hc) := by
      rw [P.map_maximalIdeal_stalk y hy hc, P.stalkEquiv_germ]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨w, hw, hwe⟩ := (Ideal.mem_map_of_equiv _ _).mp h2
    rw [(P.stalkEquiv y hy hc).injective hwe] at hw
    exact hw
  let ψ : MvPolynomial (Fin P.n) ℂ →+* ℂ := φ.comp P.secHom
  have hψ : ∀ g, ψ g = val sW (P.secHom g) y hy := fun g => hφ _
  have hC : ∀ c, ψ (C c) = c := fun c => by
    rw [hψ, secHom_C, val_const sW P.V y hy hc]
  have hX : ∀ j, ψ (MvPolynomial.X j) = P.coord y hy j := fun j => by
    have hm : X j - C (P.coord y hy j) ∈ ptIdeal (P.coord y hy) := by
      simp [ptIdeal, RingHom.mem_ker]
    have := hker _ hm
    rw [← hψ, map_sub, hC, sub_eq_zero] at this
    exact this
  have hext : ψ = MvPolynomial.eval (P.coord y hy) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [hC, eval_C]
    · intro j; rw [hX, eval_X]
  rw [← hψ, hext]

end AffPres

theorem exists_ratio_core {S T : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) (t : T ⟶ Spec (.of ℂ))
    (g : S ⟶ T) (hg : g ≫ t = s) [LocallyOfFiniteType s] [LocallyOfFiniteType t]
    (V : T.Opens) (hV : IsAffineOpen V) {σ : Type} (u : σ → Γ(T, V))
    (hu : ∀ a : Γ(T, V), ∃ F : MvPolynomial σ ℂ, a = eval₂ (constSec t V) u F)
    {ι : Type} [Finite ι] (Ω : S.Opens) (e : ι → Γ(S, Ω)) (x : S) (hxΩ : x ∈ Ω)
    (hxV : g.base x ∈ V) (hc : IsClosed ({x} : Set S))
    (hsurj : Function.Surjective (g.stalkMap x)) :
    ∃ O : S.Opens, x ∈ O ∧ O ≤ Ω ⊓ g ⁻¹ᵁ V ∧
      ∃ (q : MvPolynomial σ ℂ) (F : ι → MvPolynomial σ ℂ),
        eval (fun a => val t (u a) (g.base x) hxV) q ≠ 0 ∧
        ∀ (y : S) (hyΩ : y ∈ Ω) (hyV : g.base y ∈ V), y ∈ O → IsClosed ({y} : Set S) →
          eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0 ∧
          ∀ i, val s (e i) y hyΩ * eval (fun a => val t (u a) (g.base y) hyV) q =
            eval (fun a => val t (u a) (g.base y) hyV) (F i) := by
  classical
  cases nonempty_fintype ι
  let z : V := ⟨g.base x, hxV⟩
  let : Algebra Γ(T, V) (T.presheaf.stalk (g.base x)) :=
    TopCat.Presheaf.algebra_section_stalk T.presheaf z
  have : IsLocalization.AtPrime (T.presheaf.stalk (g.base x)) (hV.primeIdealOf z).asIdeal :=
    hV.isLocalization_stalk z
  have hw : ∀ i, ∃ w : T.presheaf.stalk (g.base x),
      g.stalkMap x w = S.presheaf.germ Ω x hxΩ (e i) := fun i => hsurj _
  choose w hw using hw
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (hV.primeIdealOf z).asIdeal.primeCompl w
  have hint' : ∀ i, ∃ a : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) a = b • w i :=
    fun i => hint i
  choose a ha using hint'
  have halg : ∀ c : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) c =
      T.presheaf.germ V (g.base x) hxV c := fun c => rfl
  have hunit : IsUnit (T.presheaf.germ V (g.base x) hxV b) := by
    rw [← halg]
    exact IsLocalization.map_units (T.presheaf.stalk (g.base x))
      (⟨b, hb⟩ : (hV.primeIdealOf z).asIdeal.primeCompl)
  let Ω' : S.Opens := Ω ⊓ g ⁻¹ᵁ V
  have hΩ'V : Ω' ≤ g ⁻¹ᵁ V := inf_le_right
  have hΩ'Ω : Ω' ≤ Ω := inf_le_left
  have hxΩ' : x ∈ Ω' := ⟨hxΩ, hxV⟩
  have hgerm : ∀ c : Γ(T, V), S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V c) =
      g.stalkMap x (T.presheaf.germ V (g.base x) hxV c) := by
    intro c
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  have hEq : ∀ i, S.presheaf.germ Ω' x hxΩ'
      (g.appLE V Ω' hΩ'V b * S.presheaf.map (homOfLE hΩ'Ω).op (e i)) =
      S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V (a i)) := by
    intro i
    rw [map_mul, hgerm, hgerm, TopCat.Presheaf.germ_res_apply, ← hw i, ← map_mul]
    congr 1
    rw [← halg, ← halg, ha i, Algebra.smul_def]
  have hO := fun i => TopCat.Presheaf.germ_eq S.presheaf x hxΩ' hxΩ' _ _ (hEq i)
  choose Oi hxOi iU iV hOi using hO
  obtain ⟨q, hq⟩ := hu b
  choose F hF using fun i => hu (a i)
  let O : S.Opens := (g ⁻¹ᵁ T.basicOpen b) ⊓ Ω' ⊓ Finset.univ.inf Oi
  have hmemO : ∀ y, y ∈ O → y ∈ g ⁻¹ᵁ T.basicOpen b ∧ y ∈ Ω' ∧ ∀ i, y ∈ Oi i := by
    intro y hy
    refine ⟨hy.1.1, hy.1.2, fun i => ?_⟩
    have h2 := hy.2
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf] at h2
    simp only [Set.iInf_eq_iInter, Set.mem_iInter] at h2
    exact h2 i (Finset.mem_univ i)

  have hne : ∀ (y : S) (hyV : g.base y ∈ V), IsClosed ({y} : Set S) →
      g.base y ∈ T.basicOpen b → eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0 := by
    intro y hyV hcy hyb
    have hcy' := isClosed_image_of_closed s t g hg y hcy
    rw [← val_eval₂ t u q _ hyV hcy', ← hq]
    intro h0
    rw [val_eq_zero_iff t b _ hyV hcy', ← Scheme.germ_residue, CommRingCat.comp_apply] at h0
    have hu' := (T.mem_basicOpen b (g.base y) hyV).mp hyb
    exact (hu'.map (T.residue (g.base y)).hom).ne_zero h0
  refine ⟨O, ?_, fun y hy => (hmemO y hy).2.1, q, F, ?_, ?_⟩
  · refine ⟨⟨?_, hxΩ'⟩, ?_⟩
    · exact (T.mem_basicOpen b (g.base x) hxV).mpr hunit
    · show x ∈ ((Finset.univ.inf Oi : S.Opens) : Set S)
      rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
      simp only [Set.iInf_eq_iInter, Set.mem_iInter]
      exact fun i _ => hxOi i
  · exact hne x hxV hc ((T.mem_basicOpen b (g.base x) hxV).mpr hunit)
  · intro y hyΩ hyV hyO hcy
    obtain ⟨hyb, hyΩ', hyOi⟩ := hmemO y hyO
    have hcy' := isClosed_image_of_closed s t g hg y hcy
    refine ⟨hne y hyV hcy hyb, fun i => ?_⟩
    obtain ⟨φ, hφ⟩ := val_ringHom s Ω' y hyΩ' hcy
    have h1 := congrArg (fun f => val s f y (hyOi i)) (hOi i)
    simp only at h1
    rw [show iU i = homOfLE (leOfHom (iU i)) from rfl, show iV i = homOfLE (leOfHom (iV i)) from rfl,
      val_restrict, val_restrict, ← hφ, map_mul, hφ, hφ, val_restrict] at h1
    rw [(val_comp s t g hg hΩ'V b y hyΩ' hcy).2, (val_comp s t g hg hΩ'V (a i) y hyΩ' hcy).2] at h1
    have e1 : val t b (g.base y) (hΩ'V hyΩ') = eval (fun a => val t (u a) (g.base y) hyV) q := by
      rw [hq]; exact val_eval₂ t u q _ hyV hcy'
    have e2 : val t (a i) (g.base y) (hΩ'V hyΩ') =
        eval (fun a => val t (u a) (g.base y) hyV) (F i) := by
      rw [hF i]; exact val_eval₂ t u (F i) _ hyV hcy'
    rw [e1, e2] at h1
    rw [mul_comm]
    exact h1

end

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

variable {W X : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)}

theorem isClosed_of_isClosed_open [LocallyOfFiniteType sW] (V : W.Opens) (x : V)
    (hx : IsClosed ({x} : Set V)) : IsClosed ({x.1} : Set W) := by
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
  apply isClosed_singleton_of_isLocallyClosed_singleton
  obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.mp hx
  refine ⟨(V : Set W), t, V.isOpen, ht, ?_⟩
  ext z
  constructor
  · rintro rfl
    exact ⟨x.2, (Set.ext_iff.mp hteq x).mpr rfl⟩
  · rintro ⟨hzV, hzt⟩
    have e : (⟨z, hzV⟩ : V) = x := (Set.ext_iff.mp hteq ⟨z, hzV⟩).mp hzt
    show z = x.1
    exact congrArg Subtype.val e

theorem bijOn_closedPoints_of_isIso (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (U : X.Opens) [IsIso (π ∣_ U)] :
    Set.BijOn π.base {x | IsClosed ({x} : Set W) ∧ π.base x ∈ U}
      {y | IsClosed ({y} : Set X) ∧ y ∈ U} := by
  let h := Scheme.homeoOfIso (asIso (π ∣_ U))
  have hb : ∀ z, (h z).1 = π.base z.1 := fun z => morphismRestrict_base_coe π U z
  refine ⟨fun x hx => ⟨isClosed_image_of_closed sW sX π hπ x hx.1, hx.2⟩, ?_, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ he
    have e1 : h ⟨x₁, hx₁.2⟩ = h ⟨x₂, hx₂.2⟩ :=
      Subtype.ext ((hb ⟨x₁, hx₁.2⟩).trans (he.trans (hb ⟨x₂, hx₂.2⟩).symm))
    exact congrArg Subtype.val (h.injective e1)
  · intro y hy
    let w := h.symm ⟨y, hy.2⟩
    have hw : h w = ⟨y, hy.2⟩ := h.apply_symm_apply _
    have hcl : IsClosed ({h w} : Set _) := by
      refine isClosed_induced_iff.mpr ⟨{y}, hy.1, Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
      · exact Subtype.ext (hz.trans (congrArg Subtype.val hw).symm)
      · exact (congrArg Subtype.val hz).trans (congrArg Subtype.val hw)
    have hcw : IsClosed ({w} : Set _) := by
      have := hcl.preimage h.continuous
      rwa [← Set.image_singleton, h.injective.preimage_image] at this
    have hW : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
    refine ⟨w.1, ⟨?_, w.2⟩, (hb w).symm.trans (congrArg Subtype.val hw)⟩
    apply isClosed_singleton_of_isLocallyClosed_singleton
    obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.mp hcw
    refine ⟨((π ⁻¹ᵁ U : W.Opens) : Set W), t, (π ⁻¹ᵁ U).isOpen, ht, ?_⟩
    ext z
    constructor
    · rintro rfl
      exact ⟨w.2, (Set.ext_iff.mp hteq w).mpr rfl⟩
    · rintro ⟨hzV, hzt⟩
      have e : (⟨z, hzV⟩ : ((π ⁻¹ᵁ U : W.Opens) : Set W)) = w := (Set.ext_iff.mp hteq ⟨z, hzV⟩).mp hzt
      show z = w.1
      exact congrArg Subtype.val e

theorem exists_coord_inv (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (U : X.Opens) [IsIso (π ∣_ U)] (PW : AffPres sW) (V : X.Opens)
    (hV : IsAffineOpen V) {σ : Type} [Finite σ] (u : σ → Γ(X, V))
    (hu : ∀ t : Γ(X, V), ∃ F : MvPolynomial σ ℂ, t = eval₂ (constSec sX V) u F)
    (x : W) (hxW : x ∈ PW.V) (hxV : π.base x ∈ V) (hxU : π.base x ∈ U)
    (hc : IsClosed ({x} : Set W)) :
    ∃ O : W.Opens, x ∈ O ∧ O ≤ PW.V ⊓ π ⁻¹ᵁ (U ⊓ V) ∧
      ∃ (q : MvPolynomial σ ℂ) (F : Fin PW.n → MvPolynomial σ ℂ),
        eval (fun t => val sX (u t) (π.base x) hxV) q ≠ 0 ∧
        ∀ (y : W) (hyW : y ∈ PW.V) (hyV : π.base y ∈ V), y ∈ O → IsClosed ({y} : Set W) →
          eval (fun t => val sX (u t) (π.base y) hyV) q ≠ 0 ∧
          ∀ l, PW.coord y hyW l * eval (fun t => val sX (u t) (π.base y) hyV) q =
            eval (fun t => val sX (u t) (π.base y) hyV) (F l) := by
  have hiso : IsIso (π.stalkMap x) := by
    let x' : (π ⁻¹ᵁ U : W.Opens) := ⟨x, hxU⟩
    have h1 : IsIso ((π ∣_ U).stalkMap x') := by
      first
      | exact inferInstance
      | exact (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion (π ∣_ U))).2 x'
    have h2 : (MorphismProperty.isomorphisms CommRingCat) ((π ∣_ U).stalkMap x') := h1
    exact (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap π U x') |>.mp h2
  obtain ⟨O, hxO, hO, q, F, hq, hF⟩ := exists_ratio_core sW sX π hπ V hV u hu PW.V
    (fun l => PW.secHom (MvPolynomial.X l)) x hxW hxV hc (ConcreteCategory.bijective_of_isIso (π.stalkMap x)).2
  refine ⟨O ⊓ π ⁻¹ᵁ U, ⟨hxO, hxU⟩, ?_, q, F, hq, ?_⟩
  · intro y hy
    exact ⟨(hO hy.1).1, hy.2, (hO hy.1).2⟩
  · intro y hyW hyV hyO hcy
    obtain ⟨h1, h2⟩ := hF y hyW hyV hyO.1 hcy
    refine ⟨h1, fun l => ?_⟩
    rw [← h2 l, PW.val_secHom y hyW hcy, eval_X]

theorem exists_coord_fwd (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (PW : AffPres sW) (V : X.Opens) {σ : Type} [Finite σ]
    (u : σ → Γ(X, V)) (x : W) (hxW : x ∈ PW.V) (hxV : π.base x ∈ V)
    (hc : IsClosed ({x} : Set W)) :
    ∃ O : W.Opens, x ∈ O ∧ O ≤ PW.V ⊓ π ⁻¹ᵁ V ∧
      ∃ (q : MvPolynomial (Fin PW.n) ℂ) (F : σ → MvPolynomial (Fin PW.n) ℂ),
        eval (PW.coord x hxW) q ≠ 0 ∧
        ∀ (y : W) (hyW : y ∈ PW.V) (hyV : π.base y ∈ V), y ∈ O → IsClosed ({y} : Set W) →
          eval (PW.coord y hyW) q ≠ 0 ∧
          ∀ t, val sX (u t) (π.base y) hyV * eval (PW.coord y hyW) q =
            eval (PW.coord y hyW) (F t) := by
  have : IsAffine PW.V.toScheme := IsAffine.of_isIso PW.iso.hom
  have hV : IsAffineOpen PW.V := this
  let u' : Fin PW.n → Γ(W, PW.V) := fun j => PW.secHom (MvPolynomial.X j)
  have hu' : ∀ a : Γ(W, PW.V), ∃ F : MvPolynomial (Fin PW.n) ℂ,
      a = eval₂ (constSec sW PW.V) u' F := by
    intro a
    obtain ⟨f, rfl⟩ := PW.secHom_surjective a
    refine ⟨f, ?_⟩
    conv_lhs => rw [← MvPolynomial.eval₂_eta f]
    rw [eval₂_comp_left]
    congr 1
    ext c
    exact PW.secHom_C c
  have hxW' : (𝟙 W : W ⟶ W).base x ∈ PW.V := hxW
  obtain ⟨O, hxO, hO, q, F, hq, hF⟩ := exists_ratio_core sW sW (𝟙 W) (Category.id_comp _) PW.V hV
    u' hu' (PW.V ⊓ π ⁻¹ᵁ V) (fun t => π.appLE V (PW.V ⊓ π ⁻¹ᵁ V) inf_le_right (u t)) x
    ⟨hxW, hxV⟩ hxW' hc (by rw [Scheme.Hom.stalkMap_id]; exact fun z => ⟨z, rfl⟩)
  have hcoord : ∀ (y : W) (hyW : y ∈ PW.V) (h : (𝟙 W : W ⟶ W).base y ∈ PW.V),
      IsClosed ({y} : Set W) → (fun a => val sW (u' a) ((𝟙 W : W ⟶ W).base y) h) = PW.coord y hyW := by
    intro y hyW h hcy
    funext j
    change val sW (PW.secHom (MvPolynomial.X j)) y hyW = _
    rw [PW.val_secHom y hyW hcy, eval_X]
  refine ⟨O, hxO, fun y hy => (hO hy).1, q, F, ?_, ?_⟩
  · rw [← hcoord x hxW hxW' hc]
    exact hq
  · intro y hyW hyV hyO hcy
    have hyW' : (𝟙 W : W ⟶ W).base y ∈ PW.V := hyW
    obtain ⟨h1, h2⟩ := hF y ⟨hyW, hyV⟩ hyW' hyO hcy
    rw [hcoord y hyW hyW' hcy] at h1 h2
    refine ⟨h1, fun t => ?_⟩
    rw [← h2 t, (val_comp sW sX π hπ inf_le_right (u t) y ⟨hyW, hyV⟩ hcy).2]

end

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

namespace AffPres

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)} (P : AffPres s)

theorem secHom_surj : Function.Surjective P.secHom := by
  intro t
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).hom (P.iso.inv.appTop (P.V.topIso.inv t)))
  refine ⟨a, ?_⟩
  show P.V.topIso.hom (P.iso.hom.appTop ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk P.K a))) = t
  rw [ha, ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply,
    ← CommRingCat.comp_apply P.iso.inv.appTop, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
    Scheme.Hom.id_appTop, CommRingCat.id_apply, ← CommRingCat.comp_apply P.V.topIso.inv, Iso.inv_hom_id,
    CommRingCat.id_apply]

theorem isAffineOpen_V' : IsAffineOpen P.V := by
  have : IsAffine P.V.toScheme := IsAffine.of_isIso P.iso.hom
  exact this

end AffPres

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)

theorem eval_val_chartCoord (p : (k : K) → ι k) (y : projX P hP) (hy : y ∈ (chartOpen hP p).1)
    (hc : IsClosed ({y} : Set (projX P hP))) (f : MvPolynomial (Σ k, ι k) ℂ) :
    eval (fun q => val (toSpecC hP) (chartCoord hP p q) y hy) f =
      val (toSpecC hP) ((gammaChart hP p).symm (Ideal.Quotient.mk _ f)) y hy := by
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP p).1 y hy hc
  have h := MvPolynomial.ringHom_ext
    (f := eval (fun q => val (toSpecC hP) (chartCoord hP p q) y hy))
    (g := φ.comp ((gammaChart hP p).symm.toRingHom.comp (Ideal.Quotient.mk (chartIdeal P p)))) ?_ ?_
  · exact (RingHom.congr_fun h f).trans (hφ _)
  · intro a
    rw [eval_C, RingHom.comp_apply, RingHom.comp_apply, hφ]
    show a = val _ ((gammaChart hP p).symm (Ideal.Quotient.mk _ (C a))) y hy
    rw [gammaChart_symm_C, val_const _ _ y hy hc]
  · intro q
    rw [eval_X, RingHom.comp_apply, RingHom.comp_apply, hφ]
    rfl

end

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

variable (w : WData P D hP)

abbrev Idx : Type := Σ p : ((k : K) → ι k), Fin (w.m p)

def M : Type := {x : w.W // IsClosed ({x} : Set w.W)}

def src (c : w.Idx) : Set w.M := {x | x.1 ∈ (w.pres c.1 c.2).V}

open Classical in

def coord (c : w.Idx) (x : w.M) : Fin (w.pres c.1 c.2).n → ℂ :=
  if h : x.1 ∈ (w.pres c.1 c.2).V then (w.pres c.1 c.2).coord x.1 h else 0

instance topology : TopologicalSpace w.M :=
  TopologicalSpace.generateFrom
    {S | ∃ (c : w.Idx) (O : Set (Fin (w.pres c.1 c.2).n → ℂ)), IsOpen O ∧ S = w.src c ∩ w.coord c ⁻¹' O}

open Classical in

def lift (c : w.Idx) (q : Σ k, ι k) : MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ :=
  if q.2 = c.1 q.1 then 1 else X (w.yq c.1 c.2 q)

theorem coord_of_mem (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    w.coord c x = (w.pres c.1 c.2).coord x.1 hx := by
  unfold coord; exact dif_pos hx

theorem eval_coord_val (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) (f : MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ) :
    eval (w.coord c x) f = val (w.π ≫ toSpecC hP) ((w.pres c.1 c.2).secHom f) x.1 hx := by
  have := w.lft
  rw [w.coord_of_mem c x hx]
  exact (w.pres c.1 c.2).eval_coord_eq_val x.1 hx x.2 f

theorem mem_basicOpen_iff (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) (f : MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ) :
    x.1 ∈ w.W.basicOpen ((w.pres c.1 c.2).secHom f) ↔ eval (w.coord c x) f ≠ 0 := by
  rw [(w.pres c.1 c.2).mem_basicOpen_secHom_iff x.1 hx f, (w.pres c.1 c.2).ptOf_eq_ptIdeal x.1 hx x.2,
    ptIdeal, RingHom.mem_ker, w.coord_of_mem c x hx]

theorem trans_strong (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c ∩ w.src c') :
    ∃ (q : MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ)
      (F : Fin (w.pres c'.1 c'.2).n → MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ),
      eval (w.coord c x) q ≠ 0 ∧ ∀ y ∈ w.src c, eval (w.coord c y) q ≠ 0 →
        y ∈ w.src c' ∧ ∀ l, w.coord c' y l * eval (w.coord c y) q = eval (w.coord c y) (F l) := by
  have := w.lft
  obtain ⟨O, hxO, hO, q0, F0, hq0, hF0⟩ := exists_coord_fwd (𝟙 w.W) (Category.id_comp _)
    (w.pres c.1 c.2) (w.pres c'.1 c'.2).V (fun l => (w.pres c'.1 c'.2).secHom (X l)) x.1 hx.1 hx.2 x.2
  obtain ⟨f, hfO, hxf⟩ := (w.pres c.1 c.2).isAffineOpen_V'.exists_basicOpen_le ⟨x.1, hxO⟩ hx.1
  obtain ⟨h, rfl⟩ := (w.pres c.1 c.2).secHom_surj f
  have hxh := (w.mem_basicOpen_iff c x hx.1 h).mp hxf
  refine ⟨q0 * h, fun l => F0 l * h, ?_, ?_⟩
  · rw [eval_mul]
    rw [w.coord_of_mem c x hx.1] at hxh ⊢
    exact mul_ne_zero hq0 hxh
  · intro y hy hne
    rw [eval_mul] at hne
    have hyh : y.1 ∈ w.W.basicOpen ((w.pres c.1 c.2).secHom h) :=
      (w.mem_basicOpen_iff c y hy h).mpr (right_ne_zero_of_mul hne)
    have hyO : y.1 ∈ O := hfO hyh
    have hy' : y.1 ∈ (w.pres c'.1 c'.2).V := (hO hyO).2
    refine ⟨hy', fun l => ?_⟩
    have e1 : val (w.π ≫ toSpecC hP) ((w.pres c'.1 c'.2).secHom (X l)) y.1 hy' *
        eval ((w.pres c.1 c.2).coord y.1 hy) q0 = eval ((w.pres c.1 c.2).coord y.1 hy) (F0 l) :=
      (hF0 y.1 hy hy' hyO y.2).2 l
    rw [← (w.pres c'.1 c'.2).eval_coord_eq_val y.1 hy' y.2, eval_X] at e1
    rw [w.coord_of_mem c y hy, w.coord_of_mem c' y hy', eval_mul, eval_mul, ← e1]
    ring

theorem pi_mem (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) : w.π.base x.1 ∈ (chartOpen hP c.1).1 :=
  w.le_pres c.1 c.2 hx

theorem pi_closed (x : w.M) : IsClosed ({w.π.base x.1} : Set (projX P hP)) := by
  have := w.lft
  exact isClosed_image_of_closed (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl x.1 x.2

theorem lift_val (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) (q : Σ k, ι k) :
    eval (w.coord c x) (w.lift c q) =
      val (toSpecC hP) (chartCoord hP c.1 q) (w.π.base x.1) (w.pi_mem c x hx) := by
  have := w.lft
  by_cases hq : q.2 = c.1 q.1
  · have e : w.lift c q = 1 := by simp [lift, hq]
    rw [e, map_one]
    obtain ⟨k, i⟩ := q
    simp only at hq
    subst hq
    have e1 : Ideal.Quotient.mk (chartIdeal P c.1) (X ⟨k, c.1 k⟩) = 1 := by
      rw [← map_one (Ideal.Quotient.mk (chartIdeal P c.1)), Ideal.Quotient.eq]
      exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    have e2 : chartCoord hP c.1 ⟨k, c.1 k⟩ = 1 := by
      rw [chartCoord, e1, map_one]
    rw [e2]
    obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP c.1).1 _ (w.pi_mem c x hx) (w.pi_closed x)
    rw [← hφ, map_one]
  · have e : w.lift c q = X (w.yq c.1 c.2 q) := by simp [lift, hq]
    rw [e, w.eval_coord_val c x hx, w.sec_yq c.1 c.2 q]
    exact (val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (w.le_pres c.1 c.2)
      (chartCoord hP c.1 q) x.1 hx x.2).2

theorem isOpen_alt_bis (c : w.Idx) : IsOpen (w.src c) := by
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  exact ⟨c, Set.univ, isOpen_univ, by rw [Set.preimage_univ, Set.inter_univ]⟩

theorem cover (x : w.M) : ∃ c, x ∈ w.src c := by
  obtain ⟨p, hp⟩ := chartOpen_cover hP (w.π.base x.1)
  have h1 : x.1 ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hp
  rw [← w.iSup_pres p] at h1
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h1
  exact ⟨⟨p, i⟩, hi⟩

theorem isEmbedding (c : w.Idx) : Topology.IsEmbedding fun y : w.src c => w.coord c y := by
  have hcont : Continuous fun y : w.src c => w.coord c y := by
    rw [continuous_def]
    intro O hO
    have h1 : IsOpen (w.src c ∩ w.coord c ⁻¹' O) :=
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨c, O, hO, rfl⟩
    exact isOpen_induced_iff.mpr ⟨_, h1, Set.ext fun y => ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩⟩
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp hcont) ?_⟩, ?_⟩
  · show TopologicalSpace.induced _ _ ≤ TopologicalSpace.induced Subtype.val
      (TopologicalSpace.generateFrom _)
    rw [induced_generateFrom_eq]
    apply le_generateFrom
    rintro _ ⟨S, ⟨c', O', hO', rfl⟩, rfl⟩
    have hloc : ∀ y : w.src c, y.1 ∈ w.src c' ∩ w.coord c' ⁻¹' O' →
        ∃ U : Set (Fin (w.pres c.1 c.2).n → ℂ), IsOpen U ∧ w.coord c y.1 ∈ U ∧
          ∀ z : w.src c, w.coord c z.1 ∈ U → z.1 ∈ w.src c' ∩ w.coord c' ⁻¹' O' := by
      rintro y ⟨hy1, hy2⟩
      obtain ⟨q, F, hq, hF⟩ := w.trans_strong c c' y.1 ⟨y.2, hy1⟩
      let g : (Fin (w.pres c.1 c.2).n → ℂ) → (Fin (w.pres c'.1 c'.2).n → ℂ) :=
        fun a l => eval a (F l) / eval a q
      have hg : ContinuousOn g {a | eval a q ≠ 0} := continuousOn_pi.mpr fun l =>
        (MvPolynomial.continuous_eval _).continuousOn.div (MvPolynomial.continuous_eval _).continuousOn
          fun a ha => ha
      have hU : IsOpen ({a | eval a q ≠ 0} ∩ g ⁻¹' O') :=
        hg.isOpen_inter_preimage (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const) hO'
      have hval : ∀ z ∈ w.src c, eval (w.coord c z) q ≠ 0 →
          z ∈ w.src c' ∧ w.coord c' z = g (w.coord c z) := by
        intro z hz hzq
        obtain ⟨h1, h2⟩ := hF z hz hzq
        exact ⟨h1, funext fun l => eq_div_of_mul_eq hzq (h2 l)⟩
      refine ⟨{a | eval a q ≠ 0} ∩ g ⁻¹' O', hU, ⟨hq, ?_⟩, fun z hz => ?_⟩
      · obtain ⟨-, h2⟩ := hval y.1 y.2 hq
        show g (w.coord c y.1) ∈ O'
        rw [← h2]
        exact hy2
      · obtain ⟨hz1, hz2⟩ := hz
        obtain ⟨h1, h2⟩ := hval z.1 z.2 hz1
        refine ⟨h1, ?_⟩
        show w.coord c' z.1 ∈ O'
        rw [h2]
        exact hz2
    choose U hUo hyU hUS using hloc
    refine isOpen_induced_iff.mpr ⟨⋃ (y : w.src c) (hy : y.1 ∈ w.src c' ∩ w.coord c' ⁻¹' O'), U y hy,
      isOpen_iUnion fun y => isOpen_iUnion fun hy => hUo y hy, ?_⟩
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, hz⟩
      exact hUS y hy z hz
    · intro hz
      exact ⟨z, hz, hyU z hz⟩
  · intro y y' h
    have hy : w.coord c y.1 = w.coord c y'.1 := h
    rw [w.coord_of_mem c y.1 y.2, w.coord_of_mem c y'.1 y'.2] at hy
    have hzero : ∀ h ∈ (w.pres c.1 c.2).K, eval ((w.pres c.1 c.2).coord y.1.1 y.2) h = 0 :=
      (w.pres c.1 c.2).eval_coord_eq_zero y.1.1 y.2 y.1.2
    obtain ⟨x0, -, huniq⟩ := (w.pres c.1 c.2).existsUnique_closed_coord _ hzero
    have e1 := huniq y.1.1 ⟨y.2, y.1.2, rfl⟩
    have e2 := huniq y'.1.1 ⟨y'.2, y'.1.2, hy.symm⟩
    exact Subtype.ext (Subtype.ext (e1.trans e2.symm))

theorem image (c : w.Idx) :
    w.coord c '' w.src c = {y | ∀ h ∈ (w.pres c.1 c.2).K, eval y h = 0} := by
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩ h hh
    rw [w.coord_of_mem c y hy]
    exact (w.pres c.1 c.2).eval_coord_eq_zero y.1 hy y.2 h hh
  · intro ha
    obtain ⟨x, ⟨hxV, hcl, hco⟩, -⟩ := (w.pres c.1 c.2).existsUnique_closed_coord a ha
    refine ⟨⟨x, hcl⟩, hxV, ?_⟩
    rw [w.coord_of_mem c ⟨x, hcl⟩ hxV]
    exact hco

theorem trans (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c ∩ w.src c') :
    ∃ (q : MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ)
      (F : Fin (w.pres c'.1 c'.2).n → MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ),
      eval (w.coord c x) q ≠ 0 ∧ ∀ y ∈ w.src c ∩ w.src c', eval (w.coord c y) q ≠ 0 →
        ∀ l, w.coord c' y l * eval (w.coord c y) q = eval (w.coord c y) (F l) := by
  obtain ⟨q, F, hq, hF⟩ := w.trans_strong c c' x hx
  exact ⟨q, F, hq, fun y hy hne => (hF y hy.1 hne).2⟩

theorem lift_one (c : w.Idx) : ∃ p : (k : K) → ι k, ∀ k, w.lift c ⟨k, p k⟩ = 1 :=
  ⟨c.1, fun k => by simp [lift]⟩

theorem lift_chartIdeal (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    ∀ h ∈ chartIdeal P c.1, eval (fun q => eval (w.coord c x) (w.lift c q)) h = 0 := by
  intro h hh
  have e : (fun q => eval (w.coord c x) (w.lift c q)) =
      fun q => val (toSpecC hP) (chartCoord hP c.1 q) (w.π.base x.1) (w.pi_mem c x hx) :=
    funext (w.lift_val c x hx)
  rw [e, eval_val_chartCoord hP c.1 _ _ (w.pi_closed x), Ideal.Quotient.eq_zero_iff_mem.mpr hh, map_zero]
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP c.1).1 _ (w.pi_mem c x hx) (w.pi_closed x)
  rw [← hφ, map_zero]

theorem lift_mem (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    (fun q => eval (w.coord c x) (w.lift c q)) ∈ conePts P := by
  exact (conePts_of_chartIdeal hP c.1 _ (w.lift_chartIdeal c x hx)).1

theorem compat (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c ∩ w.src c') :
    SameOrbit (fun q => eval (w.coord c x) (w.lift c q)) (fun q => eval (w.coord c' x) (w.lift c' q)) := by
  have := w.lft
  have hpp : w.π.base x.1 ∈ (chartOpen hP c.1).1 ⊓ (chartOpen hP c'.1).1 :=
    ⟨w.pi_mem c x hx.1, w.pi_mem c' x hx.2⟩
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) _ _ hpp (w.pi_closed x)
  have key : ∀ q, eval (w.coord c x) (w.lift c q) * eval (w.coord c' x) (w.lift c' ⟨q.1, c.1 q.1⟩) =
      eval (w.coord c' x) (w.lift c' q) := by
    intro q
    rw [w.lift_val c x hx.1, w.lift_val c' x hx.2, w.lift_val c' x hx.2]
    have e := congrArg φ (chartCoord_overlap hP c.1 c'.1 q)
    rw [map_mul, hφ, hφ, hφ, val_restrict, val_restrict, val_restrict] at e
    exact e
  have one' : ∀ k, eval (w.coord c' x) (w.lift c' ⟨k, c'.1 k⟩) = 1 := fun k => by simp [lift]
  have hd : ∀ k, eval (w.coord c' x) (w.lift c' ⟨k, c.1 k⟩) ≠ 0 := by
    intro k h0
    have e := key ⟨k, c'.1 k⟩
    rw [h0, mul_zero, one' k] at e
    exact zero_ne_one e
  refine ⟨fun k => (eval (w.coord c' x) (w.lift c' ⟨k, c.1 k⟩))⁻¹, fun k => inv_ne_zero (hd k),
    funext fun q => ?_⟩
  show eval (w.coord c x) (w.lift c q) =
    (eval (w.coord c' x) (w.lift c' ⟨q.1, c.1 q.1⟩))⁻¹ * eval (w.coord c' x) (w.lift c' q)
  rw [eq_inv_mul_iff_mul_eq₀ (hd q.1), mul_comm]
  exact key q

theorem regular_coord (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    IsRegularLocalRing (locRing (w.pres c.1 c.2).K (w.coord c x)) := by
  rw [w.coord_of_mem c x hx]
  exact ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x.1 hx x.2).mp (w.regular x.1)

end WData

end

end ReciprocityTheory.AnForm.R
end
