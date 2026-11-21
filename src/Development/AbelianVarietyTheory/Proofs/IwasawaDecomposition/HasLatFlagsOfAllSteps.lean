import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAt

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocM.LatNorm

theorem fromSpec_appLE_top' {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem val_appLE {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {k : Type} [CommRing k]
    (φ : Γ(X, U) →+* k) (g : X ⟶ Y) {O : Y.Opens} (hle : U ≤ g ⁻¹ᵁ O)
    (h : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g) ⁻¹ᵁ O) (s : Γ(Y, O)) :
    (Scheme.ΓSpecIso (.of k)).hom (((spMap φ ≫ hU.fromSpec) ≫ g).appLE O ⊤ h s) = φ (g.appLE O U hle s) := by
  have e₀ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have e₁ : ⊤ ≤ spMap φ ⁻¹ᵁ (⊤ : (Sp Γ(X, U)).Opens) := le_top
  have e : ((spMap φ ≫ hU.fromSpec) ≫ g).appLE O ⊤ h =
      g.appLE O U hle ≫ hU.fromSpec.appLE U ⊤ e₀ ≫ (spMap φ).appLE ⊤ ⊤ e₁ := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  have h1 : (spMap φ).appLE ⊤ ⊤ e₁ = (spMap φ).appTop := Scheme.Hom.appLE_eq_app _
  rw [e, fromSpec_appLE_top', h1]
  have := congrArg (fun f => f.hom ((Scheme.ΓSpecIso Γ(X, U)).inv (g.appLE O U hle s)))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.comp_apply] at this ⊢
  refine this.trans ?_
  exact congrArg φ (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(X, U)) _)

open GlobalTheory.Twist (resM app_resM)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem tanEv_incl_res {B : Mdl Y i₀} (L : Lat B) {k : Type} [CommRing k] {x : Sp k ⟶ B.X}
    {v : Sp (DualNumber k) ⟶ B.t.G.left} (hv : IsTanAtG B.t x v) {V O : B.X.Opens} (hOV : O ≤ V)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (hO : ⊤ ≤ x ⁻¹ᵁ O) (s : Γ(L.N.toMod, V)) :
    tanEv B.t hv h (L.N.incl.app V s) = tanEv B.t hv hO (L.N.incl.app O (resM _ hOV s)) := by
  rw [app_resM, tanEv_resM]

theorem tanEv_incl_sum {B : Mdl Y i₀} (L : Lat B) {k : Type} [CommRing k] {x : Sp k ⟶ B.X}
    {v : Sp (DualNumber k) ⟶ B.t.G.left} (hv : IsTanAtG B.t x v) {O : B.X.Opens} (hO : ⊤ ≤ x ⁻¹ᵁ O) {n : ℕ}
    (c : Fin n → Γ(B.X, O)) (s : Fin n → Γ(L.N.toMod, O)) :
    tanEv B.t hv hO (L.N.incl.app O (∑ i, c i • s i)) =
      ∑ i, (Scheme.ΓSpecIso (.of k)).hom (x.appLE O ⊤ hO (c i)) * tanEv B.t hv hO (L.N.incl.app O (s i)) := by
  let f : Γ(B.om, O) →+ k := AddMonoidHom.mk' (tanEv B.t hv hO) (tanEv_add B.t hv hO)
  have e : tanEv B.t hv hO (L.N.incl.app O (∑ i, c i • s i)) = f (L.N.incl.app O (∑ i, c i • s i)) := rfl
  rw [e, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul]
  exact tanEv_smul B.t hv hO _ _

theorem stepAt_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (σ : E →+* ℂ) (r : ℕ) (hr : r ≤ Dw.mult σ) (g : Z.X ⟶ B.X), IsMap Z B g → Step.Holds ⟨B, L, σ, r, hr⟩ Z → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ x : Z.X, g x ∈ V → ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (a : GL (Fin n) Γ(Z.X, U)), x ∈ U ∧ U ≤ g ⁻¹ᵁ V ∧ LatCover.StepAt Z B g L σ r hU m a := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L σ r hr g hg hH V n m hm x hx
  obtain ⟨-, g', hg', hS⟩ := hH
  dsimp only at g' hg' hS
  obtain rfl := GlobalTheory.LocM.MapUniq.isMap_unique E H Dw Xo p W Y i₀ hp hW Z B g' g hg' hg
  obtain ⟨U', hU', V', n', m', a', hxU', hU'V', hm', hcl⟩ := hS x
  have hxO : g' x ∈ V ⊓ V' := ⟨hx, hU'V' hxU'⟩
  haveI : Nontrivial Γ(B.X, V ⊓ V') := (B.X.presheaf.germ (V ⊓ V') (g' x) hxO).hom.domain_nontrivial
  let b := hm.basis (inf_le_left : V ⊓ V' ≤ V)
  let b' := hm'.basis (inf_le_right : V ⊓ V' ≤ V')
  obtain rfl : n = n' := by simpa using Fintype.card_congr (b.indexEquiv b')
  obtain ⟨U, hU, hxU, hUle⟩ := GlobalTheory.QCoh.exists_affine_mem_le (U := U' ⊓ g' ⁻¹ᵁ (V ⊓ V')) x ⟨hxU', hxO⟩
  have hUU' : U ≤ U' := hUle.trans inf_le_left
  have hUO : U ≤ g' ⁻¹ᵁ (V ⊓ V') := hUle.trans inf_le_right
  have hUV : U ≤ g' ⁻¹ᵁ V := hUO.trans (g'.preimage_mono inf_le_left)
  let gU : Γ(B.X, V ⊓ V') →+* Γ(Z.X, U) := (g'.appLE (V ⊓ V') U hUO).hom
  let T := b.toMatrix b'
  let S := b'.toMatrix b
  let Mu : GL (Fin n) Γ(Z.X, U) := ⟨(T.map gU).transpose, (S.map gU).transpose,
    by rw [← Matrix.transpose_mul, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ gU.map_zero gU.map_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ gU.map_zero gU.map_one, Matrix.transpose_one]⟩
  let a : GL (Fin n) Γ(Z.X, U) := Matrix.GeneralLinearGroup.map (GlobalTheory.LocM.StepFrame.resR hUU') a' * Mu
  refine ⟨U, hU, a, hxU, hUV, ?_⟩
  intro k _ φ v hv h hin j hj
  have ept : spMap (φ.comp (GlobalTheory.LocM.StepFrame.resR hUU')) ≫ hU'.fromSpec = spMap φ ≫ hU.fromSpec := by
    have sc : spMap (φ.comp (GlobalTheory.LocM.StepFrame.resR hUU')) = spMap φ ≫ spMap (GlobalTheory.LocM.StepFrame.resR hUU') := by
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [sc, Category.assoc, GlobalTheory.LocM.StepFrame.spMap_resR hU' hU hUU']
  have key := hcl k (φ.comp (GlobalTheory.LocM.StepFrame.resR hUU')) v
  rw [ept] at key
  have hfU : ⊤ ≤ (spMap φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    exact le_rfl
  have hO : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g') ⁻¹ᵁ (V ⊓ V') := by
    rw [Scheme.Hom.comp_preimage]
    exact hfU.trans ((spMap φ ≫ hU.fromSpec).preimage_mono hUO)
  have hV' : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g') ⁻¹ᵁ V' := hO.trans (Scheme.Hom.preimage_mono _ inf_le_right)
  have k0 := key hv hV' hin j hj

  have hb : ∀ l, b l = resM _ (inf_le_left : V ⊓ V' ≤ V) (m l) := fun l => hm.basis_apply _ _
  have hb' : ∀ l, b' l = resM _ (inf_le_right : V ⊓ V' ≤ V') (m' l) := fun l => hm'.basis_apply _ _
  have e₁ : ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = tanEv B.t hv hO (L.N.incl.app (V ⊓ V') (b l)) := fun l => by
    rw [hb]
    exact tanEv_incl_res L hv inf_le_left h hO (m l)
  have e₂ : ∀ l', tanEv B.t hv hV' (L.N.incl.app V' (m' l')) =
      ∑ i, φ (gU (T i l')) * tanEv B.t hv hO (L.N.incl.app (V ⊓ V') (b i)) := fun l' => by
    rw [tanEv_incl_res L hv inf_le_right hV' hO (m' l'), ← hb', ← b.sum_toMatrix_smul_self b' l', tanEv_incl_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [val_appLE hU φ g' hUO]
  have e₃ : ∀ l, φ (a j l) = ∑ l', φ (GlobalTheory.LocM.StepFrame.resR hUU' (a' j l')) * φ (gU (T l l')) := fun l => by
    have ea : (a : Matrix (Fin n) (Fin n) Γ(Z.X, U)) = (Matrix.GeneralLinearGroup.map (GlobalTheory.LocM.StepFrame.resR hUU') a' :
        Matrix (Fin n) (Fin n) Γ(Z.X, U)) * (Mu : Matrix (Fin n) (Fin n) Γ(Z.X, U)) := Units.val_mul _ _
    rw [ea, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [map_mul]
    rfl
  simp only [e₂, RingHom.comp_apply] at k0
  simp only [e₁, e₃, Finset.sum_mul, Finset.mul_sum, mul_assoc] at k0 ⊢
  rw [Finset.sum_comm]
  exact k0

end GlobalTheory.LocM.LatNorm
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_step_frame_fiber : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (σ : E →+* ℂ) (r : ℕ) (hr : r ≤ Dw.mult σ) (g : Z.X ⟶ B.X), IsMap Z B g → Step.Holds ⟨B, L, σ, r, hr⟩ Z → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ x : Z.X, g x ∈ V → ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (a : GL (Fin n) Γ(Z.X, U)), x ∈ U ∧ U ≤ g ⁻¹ᵁ V ∧ LatCover.StepAt Z B g L σ r hU m a := by
  atlas_forward_decl GlobalTheory.LocM.LatNorm.stepAt_of_frame
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv TanM)
open GlobalTheory.LieMet (tanOf isTan_tv tan_ext pushE left_pushE)

namespace GlobalTheory.LocM.LatCover

theorem exists_coordEquiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L g hg V n m hm k _ x h hx τ mu hπ
  have hgen : ⊤ ≤ (x ≫ g) ⁻¹ᵁ B.genO := by
    intro z _
    have hz : x z ∈ Z.genO := CommonMod.mem_genO_of_mem_opn hp.ne_zero Z (hx ⟨z, rfl⟩)
    rw [← CommonMod.preimage_genO g] at hz
    exact hz
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ (V ⊓ B.genO) := fun z hz => ⟨h hz, hgen hz⟩
  let m' : Fin n → Γ(GlobalTheory.LieVB.omega B.t.G, V ⊓ B.genO) :=
    fun l => GlobalTheory.Twist.resM _ inf_le_left (L.N.incl.app V (m l))
  have hm' : GlobalTheory.VB.IsFrame m' := by
    refine (hm.res (inf_le_left : V ⊓ B.genO ≤ V)).map_of_linearEquiv
      (fun U hU => LinearEquiv.ofBijective (GlobalTheory.QCoh.appLinear L.N.incl U)
        ⟨L.N.incl_app_injective U, fun s => L.N.mem_sec_iff.1 (by
          rw [L.gen U (hU.trans inf_le_right)]
          trivial)⟩) fun U hU i => ?_

    show L.N.incl.app U (GlobalTheory.Twist.resM _ hU (GlobalTheory.Twist.resM _ inf_le_left (m i))) =
      GlobalTheory.Twist.resM _ hU (GlobalTheory.Twist.resM _ inf_le_left (L.N.incl.app V (m i)))
    rw [GlobalTheory.Twist.app_resM, GlobalTheory.Twist.app_resM]
  have tcomb : ∀ (r : ℕ) (u : Fin r → TanM (x ≫ g) B.t.G) (a : Fin r → k) (l : Fin n),
      tanEv B.t (isTan_tv (∑ i, a i • u i)) h' (m' l) = ∑ i, a i * tanEv B.t (isTan_tv (u i)) h' (m' l) :=
    fun r u a l => GlobalTheory.LocM.tanEv_comb E H B.X B.t k (x ≫ g) _ h' r (fun i => (tv (u i)).left)
      (fun i => isTan_tv (u i)) a _ (isTan_tv _) ((GlobalTheory.LieMet.isComb_iff u a _).2 rfl) (m' l)
  let ev : TanM (x ≫ g) B.t.G →ₗ[k] (Fin n → k) :=
    { toFun := fun v l => tanEv B.t (isTan_tv v) h' (m' l)
      map_add' := fun v w => funext fun l => by
        have e := tcomb 2 ![v, w] ![1, 1] l
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, _root_.one_mul] at e
        exact e
      map_smul' := fun c v => funext fun l => by
        have e := tcomb 1 ![v] ![c] l
        simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at e
        exact e }
  have hev : Function.Bijective ev := by
    constructor
    · intro v w hvw
      have u := (GlobalTheory.TanFibre.existsUnique_tanEv E H B.X B.t k (x ≫ g) _ h' n m' hm' (ev v)).unique
        ⟨isTan_tv v, fun l => rfl⟩ ⟨isTan_tv w, fun l => (congrFun hvw l).symm⟩
      exact tan_ext u
    · intro c
      obtain ⟨u, ⟨hu, hval⟩, -⟩ := GlobalTheory.TanFibre.existsUnique_tanEv E H B.X B.t k (x ≫ g) _ h' n m' hm' c
      exact ⟨tanOf hu, funext hval⟩
  have hB : (x ≫ g) ≫ B.π = (x ≫ Z.π) ≫ τ := by
    rw [Category.assoc, Category.assoc, hπ]
  refine ⟨(pushE mu (x ≫ Z.π) rfl).trans ((pushE B.tMap (x ≫ g) hB).symm.trans (LinearEquiv.ofBijective ev hev)),
    fun w => ⟨_, isTan_tv ((pushE B.tMap (x ≫ g) hB).symm (pushE mu (x ≫ Z.π) rfl w)), ?_, fun l => ?_⟩⟩
  · rw [← left_pushE B.tMap (x ≫ g) hB, LinearEquiv.apply_symm_apply]
    rfl
  · exact (GlobalTheory.LocM.tanEv_resM B.t _ h' inf_le_left _).symm

end GlobalTheory.LocM.LatCover
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_fiber_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l := by
  atlas_forward_decl GlobalTheory.LocM.LatCover.exists_coordEquiv
end

section
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open GlobalTheory.LocM.MapComp GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)

namespace GlobalTheory.LocM.LatCover

theorem exists_frame_of_rows : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (U : Z.X.Opens) (hU : IsAffineOpen U) (V : B.X.Opens), U ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (a : ∀ σ : E →+* ℂ, Fin (Dw.mult σ + 1) → GL (Fin n) Γ(Z.X, U)), (∀ σ (r : Fin (Dw.mult σ + 1)), LatCover.StepAt Z B g L σ r hU m (a σ r)) → ∀ (c : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → Γ(Z.X, U)), (∀ σ, ∃ (M : GL (Fin n) Γ(Z.X, U)) (e : Fin (Dw.mult σ) ↪ Fin n), ∀ i l, M (e i) l = c σ i l) → (∀ σ (i : Fin (Dw.mult σ)), ∃ j : Fin n, (j : ℕ) < i + 1 ∧ ∀ l, c σ i l = ((a σ i.succ)⁻¹ : GL (Fin n) Γ(Z.X, U)) l j) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X), ⊤ ≤ x ⁻¹ᵁ U → Set.range x ⊆ Z.opn → ∃ u, Z.FlagAt x u ∧ HasCoord g L m x u fun σ i l => valR x U (c σ i l) := by
  intro hΦ E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L g hg U hU V hUV n m hm a hst c hext hrow k _ x hxU hxo
  classical
  obtain ⟨φx, hφ, hval⟩ : ∃ φ : Γ(Z.X, U) →+* k, spMap φ ≫ hU.fromSpec = x ∧ ∀ f, valR x U f = φ f :=
    ⟨_, GlobalTheory.FlagMod.spMap_ev x hU hxU, fun f => by rw [valR, dif_pos hxU]; rfl⟩
  obtain ⟨τ, mu, htr, hπ⟩ := StepBasis.exists_isTrans hg (x (IsLocalRing.closedPoint k))
  have h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V := GlobalTheory.FlagMod.le_preimage_map g hUV hxU
  obtain ⟨Φ, hΦw⟩ := hΦ E H Dw Xo p W hp hW Y i₀ Z B L g hg V n m hm k x h hxo τ mu hπ
  obtain ⟨a0, ψ0, h0⟩ := Z.exists_chart x hxo
  have fu0 := CommonMod.flagAt_chart Z h0
  have fu0' := fu0
  set u0 := (Z.fr a0).bc ψ0 with hu0
  obtain ⟨b, χ, hb, fr, sf⟩ := fu0

  let w : Vecs Dw (Y Z.i).t k := fun σ i => (tv (Φ.symm fun l => φx (c σ i l))).left
  have hwT : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (w σ i) := fun σ i => GlobalTheory.LieMet.isTan_tv _

  have hco : HasCoord g L m x w fun σ i l => valR x U (c σ i l) := by
    refine ⟨τ, mu, h, htr, fun σ i => ?_⟩
    obtain ⟨v, hv, e1, e2⟩ := hΦw (Φ.symm fun l => φx (c σ i l))
    exact ⟨v, hv, e1, fun l => by rw [e2, LinearEquiv.apply_symm_apply]; exact (hval _).symm⟩

  have hB : ∀ σ, ∃ (n' : ℕ) (v : Fin n' → (Sp (DualNumber k) ⟶ (Y Z.i).t.G.left)) (e : Fin (Dw.mult σ) ↪ Fin n'),
      (∀ i, v (e i) = w σ i) ∧ StepFrame.Bas (Y Z.i).t (x ≫ Z.π) v := by
    intro σ
    obtain ⟨M, e, hM⟩ := hext σ
    refine ⟨n, fun j => (tv (Φ.symm fun l => φx (M j l))).left, e, fun i => ?_, ?_⟩
    · show (tv (Φ.symm fun l => φx (M (e i) l))).left = (tv (Φ.symm fun l => φx (c σ i l))).left
      simp only [hM]
    · rw [StepFrame.bas_iff_full (fun j => GlobalTheory.LieMet.isTan_tv _)]
      have ee : (fun j => GlobalTheory.LieMet.tanOf (GlobalTheory.LieMet.isTan_tv (Φ.symm fun l => φx (M j l)))) =
          fun j => Φ.symm fun l => φx (M j l) := funext fun j => GlobalTheory.LieMet.tan_ext rfl
      rw [ee]
      have hli : LinearIndependent k fun j => Φ.symm fun l => φx (M j l) := by
        have hu : IsUnit (((M : Matrix (Fin n) (Fin n) Γ(Z.X, U))).map φx) :=
          (Matrix.GeneralLinearGroup.map φx M).isUnit
        exact (Matrix.linearIndependent_rows_of_isUnit hu).map' Φ.symm.toLinearMap Φ.symm.ker
      have : Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G) := Module.Finite.equiv Φ.symm
      refine (StepFrame.uniq_iff _).2 ⟨hli, hli.span_eq_top_of_card_eq_finrank' ?_⟩
      rw [LinearEquiv.finrank_eq Φ, Module.finrank_fin_fun, Fintype.card_fin]

  have hW : ∀ σ (i : Fin (Dw.mult σ)), ∃ cf : Fin (Dw.mult σ) → k,
      (∀ j : Fin (Dw.mult σ), (i : ℕ) + 1 ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG (Y Z.i).t (x ≫ Z.π) (u0 σ) cf (w σ i) := by
    intro σ i
    obtain ⟨j0, hj0, hcj⟩ := hrow σ i
    let A := a σ i.succ
    let col : Fin n → (Sp (DualNumber k) ⟶ (Y Z.i).t.G.left) := fun j =>
      (tv (Φ.symm fun l => φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j))).left
    have hst' := hst σ i.succ k φx
    rw [hφ] at hst'
    have hstep : ∀ i' : Fin (Dw.mult σ), (i' : ℕ) < (i : ℕ) + 1 → ∃ cf : Fin n → k,
        (∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG (Y Z.i).t (x ≫ Z.π) col cf (u0 σ i') := by
      intro i' hi'
      let w' := GlobalTheory.LieMet.tanOf (fr.1 σ i').1
      obtain ⟨v, hv, e1, e2⟩ := hΦw w'
      have hz := hst' v hv h ⟨τ, mu, u0, i', htr, fu0', by simpa using hi', e1⟩
      refine ⟨fun j => ∑ l, φx (A j l) * Φ w' l, fun j hj => ?_, ?_⟩
      · have := hz j (by simpa using hj)
        simpa only [e2] using this
      · refine (GlobalTheory.LieMet.isComb_iff (fun j => Φ.symm fun l => φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j)) _ w').2 ?_
        apply Φ.injective
        rw [map_sum]
        simp only [map_smul, LinearEquiv.apply_symm_apply]
        funext l
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have hI : ((A⁻¹ : GL (Fin n) Γ(Z.X, U)) : Matrix (Fin n) (Fin n) Γ(Z.X, U)) * (A : Matrix (Fin n) (Fin n) Γ(Z.X, U)) = 1 :=
          Units.inv_mul A
        have hinv : ∀ l', ∑ j, φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j) * φx (A j l') = if l = l' then 1 else 0 := by
          intro l'
          have := congrArg φx (congrFun (congrFun hI l) l')
          rw [Matrix.mul_apply, map_sum] at this
          simp only [map_mul] at this
          rw [this, Matrix.one_apply]
          split_ifs <;> simp
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        have : ∀ l', ∑ j, φx (A j l') * Φ w' l' * φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j) =
            (if l = l' then 1 else 0) * Φ w' l' := fun l' => by
          rw [← hinv l', Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
        simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hr : (i : ℕ) + 1 ≤ Dw.mult σ := i.2
    obtain ⟨-, hsp⟩ := StepFrame.step_eq fr hr (fun j => GlobalTheory.LieMet.isTan_tv _) hstep
    obtain ⟨cf, hcf, hcomb⟩ := hsp j0 hj0
    refine ⟨cf, hcf, ?_⟩
    have ew : w σ i = col j0 := by
      show (tv (Φ.symm fun l => φx (c σ i l))).left = _
      simp only [hcj]
      rfl
    rw [ew]
    exact hcomb
  have key := StepFrame.isFrame_of_steps fr Z.ty hW hB
  exact ⟨w, ⟨b, χ, hb, key.1, sameFlag_trans (tan_chart Z hb) (fun σ j => (fr.1 σ j).1) (fun σ j => (key.1.1 σ j).1)
    sf key.2⟩, hco⟩

end GlobalTheory.LocM.LatCover
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_fiber_basis : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (U : Z.X.Opens) (hU : IsAffineOpen U) (V : B.X.Opens), U ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (a : ∀ σ : E →+* ℂ, Fin (Dw.mult σ + 1) → GL (Fin n) Γ(Z.X, U)), (∀ σ (r : Fin (Dw.mult σ + 1)), LatCover.StepAt Z B g L σ r hU m (a σ r)) → ∀ (c : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → Γ(Z.X, U)), (∀ σ, ∃ (M : GL (Fin n) Γ(Z.X, U)) (e : Fin (Dw.mult σ) ↪ Fin n), ∀ i l, M (e i) l = c σ i l) → (∀ σ (i : Fin (Dw.mult σ)), ∃ j : Fin n, (j : ℕ) < i + 1 ∧ ∀ l, c σ i l = ((a σ i.succ)⁻¹ : GL (Fin n) Γ(Z.X, U)) l j) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X), ⊤ ≤ x ⁻¹ᵁ U → Set.range x ⊆ Z.opn → ∃ u, Z.FlagAt x u ∧ HasCoord g L m x u fun σ i l => valR x U (c σ i l) := by
  atlas_forward_decl GlobalTheory.LocM.LatCover.exists_frame_of_rows
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

namespace GlobalTheory.LocM.LatCover

theorem mult_le_rank : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (U : Z.X.Opens) (hU : IsAffineOpen U) (V : B.X.Opens), U ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (σ : E →+* ℂ) (a : GL (Fin n) Γ(Z.X, U)), LatCover.StepAt Z B g L σ (Dw.mult σ) hU m a → ∀ x : Z.X, x ∈ U → Dw.mult σ ≤ n := by
  intro hc E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L g hg U hU V hUV n m hm σ a _ x hx
  obtain ⟨k, _, φ, u, hu⟩ := GlobalTheory.LocM.StepFrame.exists_flagAt Z hU hx
  obtain ⟨τ, mu, -, hπ⟩ := GlobalTheory.LocM.StepBasis.exists_isTrans hg x
  have ho : Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn := GlobalTheory.LocM.MapComp.range_subset_opn Z hu
  have h : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g) ⁻¹ᵁ V := by
    have h1 : ⊤ ≤ (spMap φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
      rintro y -
      exact hU.range_fromSpec.le ⟨spMap φ y, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rintro y -
    have := hUV (h1 (Set.mem_univ y))
    simpa [Scheme.Hom.comp_apply] using this
  obtain ⟨Φ, -⟩ := hc E H Dw Xo p W hp hW Y i₀ Z B L g hg V n m hm k (spMap φ ≫ hU.fromSpec) h ho τ mu hπ
  obtain ⟨a₀, ψ₀, -, fu, -⟩ := hu
  by_contra hlt
  push_neg at hlt
  let b : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM ((spMap φ ≫ hU.fromSpec) ≫ Z.π) (Y Z.i).t.G :=
    fun j => Φ.symm (Pi.single j 1)
  have hcomb : ∀ i : Fin (Dw.mult σ), (i : ℕ) < Dw.mult σ → ∃ cf : Fin n → k,
      (∀ j : Fin n, Dw.mult σ ≤ (j : ℕ) → cf j = 0) ∧
      IsCombAtG (Y Z.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z.π) (fun j => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (b j)).left) cf (u σ i) := by
    intro i _
    have ht : IsTanAtG (Y Z.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z.π) (u σ i) := (fu.1 σ i).1
    refine ⟨fun j => Φ (GlobalTheory.LieMet.tanOf ht) j, fun j hj => absurd (hj.trans_lt j.2) (lt_asymm hlt), ?_⟩
    refine (GlobalTheory.LieMet.isComb_iff b _ (GlobalTheory.LieMet.tanOf ht)).2 ?_
    apply Φ.injective
    ext l
    simp [b, map_sum, Pi.single_apply]
  have hs := GlobalTheory.LocM.StepFrame.step_eq fu le_rfl (fun j => GlobalTheory.LieMet.isTan_tv (b j)) hcomb
  omega

end GlobalTheory.LocM.LatCover
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_fiber_injective : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (U : Z.X.Opens) (hU : IsAffineOpen U) (V : B.X.Opens), U ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (σ : E →+* ℂ) (a : GL (Fin n) Γ(Z.X, U)), LatCover.StepAt Z B g L σ (Dw.mult σ) hU m a → ∀ x : Z.X, x ∈ U → Dw.mult σ ≤ n := by
  atlas_forward_decl GlobalTheory.LocM.LatCover.mult_le_rank
end

section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open GlobalTheory.LocM.MapComp

namespace GlobalTheory.LocM.LatCover

theorem stepAt_res : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (g : Z.X ⟶ B.X) (L : Lat B) (σ : E →+* ℂ) (r : ℕ) (U U' : Z.X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hle : U' ≤ U) (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)) (a : GL (Fin n) Γ(Z.X, U)), LatCover.StepAt Z B g L σ r hU m a → LatCover.StepAt Z B g L σ r hU' m (Matrix.GeneralLinearGroup.map (Z.X.presheaf.map (homOfLE hle).op).hom a) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z B g L σ r U U' hU hU' hle V n m a hs k _ φ v hv h hin j hj
  have e : spMap (φ.comp (Z.X.presheaf.map (homOfLE hle).op).hom) ≫ hU.fromSpec = spMap φ ≫ hU'.fromSpec := by
    rw [← sp_comp, Category.assoc, StepFrame.spMap_resR hU hU' hle]
  have key := hs k (φ.comp (Z.X.presheaf.map (homOfLE hle).op).hom)
  rw [e] at key
  exact key v hv h hin j hj

theorem exists_rows : ∀ (R K : Type) [CommRing R] [Field K] (φ : R →+* K) (n g : ℕ) (hg : g ≤ n) (A : Fin (g + 1) → GL (Fin n) R), ∃ M : Matrix (Fin n) (Fin n) R, φ M.det ≠ 0 ∧ ∀ i : Fin g, ∃ j : Fin n, (j : ℕ) < i + 1 ∧ ∀ l, M (Fin.castLE hg i) l = ((A i.succ)⁻¹ : GL (Fin n) R) l j := by
  intro R K _ _ φ n g hg A
  classical
  let κ : Fin n → Fin (g + 1) := fun i => ⟨min (i + 1) g, by omega⟩
  let col : Fin (g + 1) → Fin n → Fin n → R := fun r j l => ((A r)⁻¹ : GL (Fin n) R) l j
  have hind : ∀ r, LinearIndependent K fun j => fun l => φ (col r j l) := by
    intro r
    have hu : IsUnit (Matrix.transpose ((((A r)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map φ)) := by
      refine (Matrix.isUnit_transpose _).2 ?_
      have := (Matrix.GeneralLinearGroup.map φ (A r)⁻¹).isUnit
      exact this
    exact Matrix.linearIndependent_rows_of_isUnit hu
  have hκ : ∀ i : Fin n, (i : ℕ) + 1 ≤ n := fun i => i.2
  obtain ⟨s, hs⟩ := StepFrame.exists_choice (k := K) n
    (fun i j => fun l => φ (col (κ i) (Fin.castLE (hκ i) j) l))
    fun i => (hind (κ i)).comp _ (Fin.castLE_injective (hκ i))
  let M : Matrix (Fin n) (Fin n) R := fun i l => col (κ i) (Fin.castLE (hκ i) (s i)) l
  refine ⟨M, ?_, fun i => ?_⟩
  · have hu : IsUnit (M.map φ) := (Matrix.linearIndependent_rows_iff_isUnit).1 hs
    rw [RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  · have e : κ (Fin.castLE hg i) = i.succ := Fin.ext (by simp [κ])
    have : ∀ r (_ : r = i.succ) (j : Fin n), (j : ℕ) < i + 1 → ∃ j' : Fin n, (j' : ℕ) < i + 1 ∧
        ∀ l, col r j l = ((A i.succ)⁻¹ : GL (Fin n) R) l j' := by
      rintro _ rfl j hj
      exact ⟨j, hj, fun l => rfl⟩
    exact this _ e _ (s _).2

theorem hasLatFlags_of_allSteps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z B : Mdl Y i₀) (L : Lat B), (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) → (∀ t ∈ allSteps L, Step.Holds t Z) → HasLatFlags Z L := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L hty h
  classical
  refine ⟨hty, fun x => ?_⟩
  obtain ⟨-, g, hg, -⟩ := h _ (mem_allSteps.2 ⟨Classical.arbitrary _, 0, Nat.zero_le _, rfl⟩)
  obtain ⟨V, n, m, hxV, hm⟩ := L.free (g x)
  choose U₀ hU₀ a₀ hx₀ hle₀ hst₀ using fun σ (r : Fin (Dw.mult σ + 1)) =>
    GlobalTheory.T.lattice_step_frame_fiber E H Dw Xo p W hp hW Y i₀ Z B L σ r (Nat.lt_succ_iff.1 r.2) g hg (h _ (mem_allSteps.2 ⟨σ, r, _, rfl⟩)) V n m hm x hxV
  have ho : IsOpen (⋂ q : Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1), (U₀ q.1 q.2 : Set Z.X)) :=
    isOpen_iInter_of_finite fun q => (U₀ q.1 q.2).2
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, hle⟩ := Z.X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_iInter.2 fun q : Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1) => hx₀ q.1 q.2) ho
  have hU : IsAffineOpen U := hU
  have hle' : ∀ σ r, U ≤ U₀ σ r := fun σ r => fun y hy => Set.mem_iInter.1 (hle hy) ⟨σ, r⟩
  let a : ∀ σ (r : Fin (Dw.mult σ + 1)), GL (Fin n) Γ(Z.X, U) := fun σ r =>
    Matrix.GeneralLinearGroup.map (Z.X.presheaf.map (homOfLE (hle' σ r)).op).hom (a₀ σ r)
  have hst : ∀ σ (r : Fin (Dw.mult σ + 1)), StepAt Z B g L σ r hU m (a σ r) := fun σ r =>
    stepAt_res E H Dw Xo p W Y i₀ Z B g L σ r _ U (hU₀ σ r) hU (hle' σ r) V n m (a₀ σ r) (hst₀ σ r)
  have hUV : U ≤ g ⁻¹ᵁ V := (hle' (Classical.arbitrary _) 0).trans (hle₀ _ _)
  have hmn : ∀ σ, Dw.mult σ ≤ n := fun σ =>
    GlobalTheory.T.lattice_frame_fiber_injective (GlobalTheory.T.lattice_frame_fiber_rank) E H Dw Xo p W hp hW Y i₀ Z B L g hg U hU V hUV n m hm σ _ (hst σ (Fin.last _)) x hx
  choose M hM hrow using fun σ =>
    exists_rows Γ(Z.X, U) (Z.X.residueField x) (Z.X.evaluation U x hx).hom n (Dw.mult σ) (hmn σ) (a σ)
  let f := ∏ σ, (M σ).det
  have hU' := hU.basicOpen f
  have hle₂ := Z.X.basicOpen_le f
  let ρ := (Z.X.presheaf.map (homOfLE hle₂).op).hom
  have hu : ∀ σ, IsUnit (ρ (M σ).det) := fun σ =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun σ => (M σ).det) (Finset.mem_univ σ)))
      (Z.X.toRingedSpace.isUnit_res_basicOpen f)
  let Mu : ∀ σ : E →+* ℂ, GL (Fin n) Γ(Z.X, Z.X.basicOpen f) := fun σ =>
    Matrix.nonsingInvUnit ((M σ).map ρ) (by show IsUnit (ρ.mapMatrix (M σ)).det; rw [← RingHom.map_det]; exact hu σ)
  let c : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → Γ(Z.X, Z.X.basicOpen f) := fun σ i l => ρ (M σ (Fin.castLE (hmn σ) i) l)
  have hext : ∀ σ, ∃ (M : GL (Fin n) Γ(Z.X, Z.X.basicOpen f)) (e : Fin (Dw.mult σ) ↪ Fin n), ∀ i l, M (e i) l = c σ i l :=
    fun σ => ⟨Mu σ, Fin.castLEEmb (hmn σ), fun i l => rfl⟩
  let a' : ∀ σ (r : Fin (Dw.mult σ + 1)), GL (Fin n) Γ(Z.X, Z.X.basicOpen f) := fun σ r =>
    Matrix.GeneralLinearGroup.map ρ (a σ r)
  have hst' : ∀ σ (r : Fin (Dw.mult σ + 1)), StepAt Z B g L σ r hU' m (a' σ r) := fun σ r =>
    stepAt_res E H Dw Xo p W Y i₀ Z B g L σ r U _ hU hU' hle₂ V n m (a σ r) (hst σ r)
  have hrow' : ∀ σ (i : Fin (Dw.mult σ)), ∃ j : Fin n, (j : ℕ) < i + 1 ∧
      ∀ l, c σ i l = ((a' σ i.succ)⁻¹ : GL (Fin n) Γ(Z.X, Z.X.basicOpen f)) l j := by
    intro σ i
    obtain ⟨j, hj, e⟩ := hrow σ i
    refine ⟨j, hj, fun l => ?_⟩
    simp only [c, a', e, ← map_inv]
    rfl
  have hUV' : Z.X.basicOpen f ≤ g ⁻¹ᵁ V := hle₂.trans hUV
  refine ⟨⟨g, hg, _, hU', V, hUV', n, m, hm, c, hext, fun k _ y hy hyo =>
    GlobalTheory.T.lattice_frame_fiber_basis (GlobalTheory.T.lattice_frame_fiber_rank) E H Dw Xo p W hp hW Y i₀ Z B L g hg _ hU' V hUV' n m hm a' hst' c hext hrow' k y hy hyo⟩, ?_⟩
  show x ∈ Z.X.basicOpen f
  rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen _ x hx, map_prod]
  exact Finset.prod_ne_zero_iff.2 fun σ _ => hM σ

end GlobalTheory.LocM.LatCover
end
end
