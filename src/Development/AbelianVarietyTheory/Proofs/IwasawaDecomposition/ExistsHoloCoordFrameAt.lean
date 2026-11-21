import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

attribute [local instance] Over.cartesianMonoidalCategory in

theorem isCombAtG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    {t : SAB H X0} {R : Type} [CommRing R] {x0 : Sp R ⟶ X0} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    {cf : Fin m → R} {w w' : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x0 v cf w)
    (h' : IsCombAtG t x0 v cf w') : w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have : u = u' := funext fun k => Over.OverMorphism.ext ((hu k).trans (hu' k).symm)
  rw [this]

theorem frameAt_v_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) (x x' : Sp ℂ ⟶ Z.X) (g : EigFrame Z σ x) (g' : EigFrame Z σ x'), FrameAt e f₀ A₀ A y g → FrameAt e f₀ A₀ A y g' → ∀ τ i, g.v τ i = g'.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ X j f₀ A₀ A y x x' g g' h h' τ i
  obtain ⟨φ, fz, ψ, hy, hc, hg⟩ := h
  obtain ⟨φ', fz', ψ', hy', hc', hg'⟩ := h'
  have hψ : ψ = ψ' := EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under y))).1 (hy.symm.trans hy'))
  subst hψ
  have hι := IsFractionRing.injective (X.X.presheaf.stalk (under y)) X.X.functionField
  obtain rfl : φ = φ' := RingHom.ext fun a => hι ((RingHom.congr_fun hc.2.1 a).symm.trans (RingHom.congr_fun hc'.2.1 a))
  obtain ⟨fK, hK⟩ := fz.exists_isMap _ hc.2.1 hc.1
  obtain ⟨fK', hK'⟩ := fz'.exists_isMap _ hc.2.1 hc.1
  have e1 : fK.co f₀ τ = fK'.co f₀ τ := by
    rw [EigFrame.co_eq (T := Matrix.of fun a k => (A₀ * A⁻¹) τ k a) fun k => by
        rw [funext (hK τ)]; exact hc.2.2 τ k,
      EigFrame.co_eq (T := Matrix.of fun a k => (A₀ * A⁻¹) τ k a) fun k => by
        rw [funext (hK' τ)]; exact hc'.2.2 τ k]
  have e2 : fK.co fK' τ = 1 := by
    rw [← fK.co_mul f₀ fK' τ, e1, fK'.co_mul, fK'.co_self]
  have e3 : fz.co fz' τ = 1 := by
    have e := (hK.co τ hK' hc.1).symm.trans e2
    ext a b
    have e' := congrFun (congrFun e a) b
    rw [Matrix.map_apply] at e'
    apply hι
    rw [e', Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e4 := fz.co_spec fz' τ i
  rw [e3] at e4
  have e5 : fz'.v τ i = fz.v τ i := isCombAtG_eq e4 (by
    convert isCombAtG_single Z.t _ (fz.tan τ) i using 2
    simp only [Matrix.one_apply, Pi.single_apply])
  rw [hg τ i, hg' τ i, e5]

end GlobalTheory.LieBase
end
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoint_stalkFrame_vectors_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) (x x' : Sp ℂ ⟶ Z.X) (g : EigFrame Z σ x) (g' : EigFrame Z σ x'), FrameAt e f₀ A₀ A y g → FrameAt e f₀ A₀ A y g' → ∀ τ i, g.v τ i = g'.v τ i := by
  atlas_forward_decl GlobalTheory.LieBase.frameAt_v_eq
end

section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolCoordEv

theorem eventually_differentiableAt_of_forms {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ}
    (W : V → Fin g → ℂ) (b₀ : V) (H : ∀ w : Fin g → ℂ, (∀ L : V → ((Fin g → ℂ) →L[ℂ] ℂ),
      (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ L b) → (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => L b (W b)) b) →
        L b₀ w = 0) → w = 0) : ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ W b := by
  let M : Submodule ℂ (Module.Dual ℂ (Fin g → ℂ)) :=
    { carrier := {l | ∃ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ L b) ∧
        (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => L b (W b)) b) ∧ ∀ w, L b₀ w = l w}
      add_mem' := by
        rintro l l' ⟨L, h1, h2, h3⟩ ⟨L', h1', h2', h3'⟩
        refine ⟨fun b => L b + L' b, ?_, ?_, fun w => by simp [h3, h3']⟩
        · filter_upwards [h1, h1'] with b hb hb' using hb.add hb'
        · filter_upwards [h2, h2'] with b hb hb' using hb.add hb'
      zero_mem' := ⟨fun _ => 0, Eventually.of_forall fun _ => differentiableAt_const _,
        Eventually.of_forall fun _ => by simp, by simp⟩
      smul_mem' := by
        rintro c l ⟨L, h1, h2, h3⟩
        refine ⟨fun b => c • L b, ?_, ?_, fun w => by simp [h3]⟩
        · filter_upwards [h1] with b hb using hb.const_smul c
        · filter_upwards [h2] with b hb using hb.const_smul c }
  have hM : M = ⊤ := by
    have h0 : M.dualCoannihilator = ⊥ := by
      refine eq_bot_iff.2 fun w hw => H w fun L h1 h2 => ?_
      exact (Submodule.mem_dualCoannihilator w).1 hw (L b₀).toLinearMap ⟨L, h1, h2, fun _ => rfl⟩
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := M), h0, Submodule.dualAnnihilator_bot]
  have hj : ∀ j : Fin g, LinearMap.proj j ∈ M := fun j => hM ▸ Submodule.mem_top
  choose L h1 h2 h3 using hj
  let J : V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun b => ContinuousLinearMap.pi fun j => L j b
  have hJ : ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ J b := by
    filter_upwards [eventually_all.2 h1] with b hb
    exact (ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).differentiableAt.comp b
      (differentiableAt_pi.2 hb)
  have hJ0 : IsUnit (J b₀) := by
    have : J b₀ = 1 := by
      ext1 w
      funext j
      exact h3 j w
    rw [this]; exact isUnit_one
  have hU : ∀ᶠ b in 𝓝 b₀, IsUnit (J b) :=
    hJ.self_of_nhds.continuousAt.eventually (Units.isOpen.mem_nhds hJ0)
  filter_upwards [hJ, hU, eventually_all.2 h2] with b hJb hUb hWb
  have hW : DifferentiableAt ℂ (fun b => J b (W b)) b := differentiableAt_pi.2 hWb
  refine ((hJb.inverse hUb).clm_apply hW).congr_of_eventuallyEq ?_
  filter_upwards [hJb.continuousAt.eventually (Units.isOpen.mem_nhds hUb)] with b' hb'
  have := congrArg (fun T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) => T (W b')) (Ring.inverse_mul_cancel _ hb')
  exact this.symm

open GlobalTheory.TangentOrigin GlobalTheory.HolLieFrame in

theorem exists_hol_snd_ev {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    (ψ : Sp (DualNumber R) ⟶ X) (ev : V → (R →+* ℂ)) (b₀ : V)
    (hev : ∀ c, ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => ev b c) b)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ (spMap (Chart.dualMapR (ev b₀)) ≫ ψ) ⁻¹ᵁ U) :
    ∃ F : V → ℂ, (∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ F b) ∧ ∀ᶠ b in 𝓝 b₀,
      ∃ h : ⊤ ≤ (spMap (Chart.dualMapR (ev b)) ≫ ψ) ⁻¹ᵁ U, (evalPt _ U h f).snd = F b := by
  have h₁ : ⊤ ≤ (spMap (fstC.comp (Chart.dualMapR (ev b₀))) ≫ ψ) ⁻¹ᵁ U := by
    have := (top_le_preimage_iff _ U).1 h₀
    rwa [← Category.assoc, ← Spec.map_comp] at this
  obtain ⟨r, a, hr, H⟩ := exists_fraction ψ U f _ h₁
  have hf : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).fst = ev b x.fst := fun b x => by simp [Chart.dualMapR]
  have hs : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).snd = ev b x.snd := fun b x => by simp [Chart.dualMapR]
  have hr' : ev b₀ r.fst ≠ 0 := (hf b₀ r) ▸ hr
  have hne : ∀ᶠ b in 𝓝 b₀, ev b r.fst ≠ 0 := (hev r.fst).self_of_nhds.continuousAt.eventually_ne hr'
  refine ⟨fun b => (ev b a.snd - ev b a.fst * (ev b r.fst)⁻¹ * ev b r.snd) * (ev b r.fst)⁻¹, ?_, ?_⟩
  · filter_upwards [hev a.snd, hev a.fst, hev r.fst, hev r.snd, hne] with b h1 h2 h3 h4 h5
    exact (h1.sub ((h2.mul (h3.inv h5)).mul h4)).mul (h3.inv h5)
  filter_upwards [hne] with b hb
  obtain ⟨h, e⟩ := H _ (Chart.dualMapR (ev b)) (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [hf]; exact hb.isUnit))
  refine ⟨h, ?_⟩
  have e1 := congrArg TrivSqZeroExt.fst e
  have e2 := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul, hf, hf] at e1
  rw [DualNumber.snd_mul, hf, hs, hs] at e2
  rw [← e1, ← e2]
  field_simp
  ring

end GlobalTheory.HolCoordEv

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_unique)

theorem eventually_differentiableAt_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) {n : ℕ}
    {B : Set (Fin n → ℂ)} (hB : IsOpen B) {P : (Fin n → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ))}
    {p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c)}
    (hu : ∀ b, Fu.u i (P b) = p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hP : ∀ b, IsPeriod (Fu.Di i) ty (P b)) (hPd : ∀ a, DifferentiableOn ℂ (fun b => P b a) B)
    (hs : ∀ b, p b ≫ pullback.snd _ _ = spMap σ) {R : Type} [CommRing R] (v : Sp (DualNumber R) ⟶ Z.t.G.left)
    (ev : (Fin n → ℂ) → (R →+* ℂ)) {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B)
    (hev : ∀ t, ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ (fun b => ev b t) b) (W : (Fin n → ℂ) → Fin g → ℂ)
    (hW : ∀ᶠ b in 𝓝 b₀, IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (Formalism.L2.Pj.dualMap (ev b)) ≫ v)) :
    ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ W b := by
  classical
  have h1 := Fu.hol i n B P hB ⟨fun b _ => hP b, hPd⟩
  have hp : IsHolTo B p := TrueCx.TorHolo.isHolTo_of_fst _ _ hB (spMap σ) hs
    (LocLift.isHolTo_congr h1.1 fun b _ => (hu b).symm)
  have h2 := TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 hB (fun b z => (Fu.ex i (P b) z).left) p h1.2 hp
    (fun b z => by rw [Over.w (Fu.ex i (P b) z), ← hu b]; rfl)
  have hFt : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) =>
      liftEx Z Fu (p bz.1) i (P bz.1) (hu bz.1) bz.2 ≫ Z.m.φ) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  have hExp : IsExpAt Z.t (p b₀ ≫ Z.jQ ≫ genι Z)
      (pushEx Z Fu (p b₀) i (P b₀) (p b₀ ≫ Z.jQ ≫ genι Z) (hu b₀) rfl) :=
    isExpAt_pushEx E H Dw l Xo c O β Z g ty _ Fu (p b₀) i (P b₀) (p b₀ ≫ Z.jQ ≫ genι Z) (hu b₀) rfl (hP b₀)
  have hW' : ∀ᶠ b in 𝓝 b₀, IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ v) := by
    filter_upwards [hW] with b hb
    rwa [← HolFrameMatrix.dualMap_eq]
  refine eventually_differentiableAt_of_forms W b₀ fun w hw => ?_
  have hw' : ∀ (O : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, O)),
      ⊤ ≤ (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) 0 ≫ Z.m.φ) ⁻¹ᵁ O →
      fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) O f) 0 w = 0 := by
    intro O f hO
    refine hw (fun b => fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) O f) 0) ?_ ?_
    · have hc : ContinuousAt (fun b : Fin n → ℂ => (b, (0 : Fin g → ℂ))) b₀ :=
        continuousAt_id.prodMk continuousAt_const
      filter_upwards [hc.preimage_mem_nhds ((hFt O f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hO⟩)] with b hb
      exact HolLieFrame.differentiableAt_fderiv
        (e := fun b z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) hFt hb.1.1 O f hb.2
    · obtain ⟨Fn, hF, hF'⟩ := exists_hol_snd_ev v ev b₀ hev O f
        ((TangentOrigin.top_le_preimage_iff _ O).2 (by rw [hW'.self_of_nhds.1]; exact hO))
      filter_upwards [hF, (hF'.and hW').eventually_nhds] with b hFb hnear
      refine hFb.congr_of_eventuallyEq ?_
      filter_upwards [hnear] with b' ⟨⟨h, e'⟩, hd⟩
      exact (hd.2 O h f).symm.trans e'
  have d₁ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) w hw'
  have d₀ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) 0
    fun _ _ _ => map_zero _
  obtain ⟨u, ⟨hut, hud⟩, -⟩ := hExp.2.1 0
  have hu0 := isDerivAt0_unique hud d₀
  obtain ⟨w', -, hw''⟩ := hExp.2.2 u hut
  have a1 : w = w' := hw'' w (by rw [hu0]; exact d₁)
  have a0 : (0 : Fin g → ℂ) = w' := hw'' 0 hud
  exact a1.trans a0.symm

end GlobalTheory.HolCoordEv
end
end

section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh

theorem exists_comb_of_exp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {σ : c.F →+* ℂ} {x x' : Sp ℂ ⟶ Z.X} (hxx : x' = x) {g : ℕ} (ex : (Fin g → ℂ) → (Over.mk x' ⟶ Z.t.G))
    (hex : IsExpAt Z.t x' ex) (f : EigFrame Z σ x) (τ : E →+* ℂ) (δ : Fin (Dw.mult τ) → Fin g → ℂ)
    (hδ : ∀ b, IsDerivAt0 (fun z => (ex z).left) (δ b) (f.v τ b)) (v' : Sp (DualNumber ℂ) ⟶ Z.t.G.left)
    (hv' : IsTanAtG Z.t x v') (heig : ∀ a, v' ≫ (Z.t.act.act a).left = spMap (epsMul (σ (embK c τ a))) ≫ v')
    (w : Fin g → ℂ) (hw : IsDerivAt0 (fun z => (ex z).left) w v') :
    ∃ a : Fin (Dw.mult τ) → ℂ, IsCombAtG Z.t x (f.v τ) a v' ∧ w = ∑ b, a b • δ b := by
  subst hxx
  obtain ⟨a, ha, -⟩ := f.basis τ v' hv' heig
  have e1 : ex 0 = 1 := by
    have h := hex.1 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hd := GlobalTheory.ShFam.Hor.ExpDirs.isDerivAt0_of_comb (congrArg (·.left) e1) (f.tan τ) hδ hv' ha
  obtain ⟨w', -, hu⟩ := hex.2.2 v' hv'
  exact ⟨a, ha, (hu w hw).trans (hu _ hd).symm⟩

end GlobalTheory.HolCoordEv

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom)

theorem coords_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (d : ℕ) (u₀ : V d) (R : Type) [CommRing R] (φR : c.F →+* R) (xR : Sp R ⟶ Z.X) (fR : EigFrame Z φR xR) (ev : V d → (R →+* ℂ)) (k : U.Comp) (G : V d → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) (τ : E →+* ℂ), (∀ t, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ev u t) u) → (∀ τ' a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → (∀ᶠ u in 𝓝 u₀, (ev u).comp φR = σ) → (∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, (cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z = spMap (ev u) ≫ xR) → ∃ M : V d → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => M u a b) u) ∧ ∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, ∀ i, IsCombAtG Z.t ((cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z) ((cxFrame Z (U.un k ⟨G u, h⟩)).v τ) (fun b => M u b i) (spMap (dualMap (ev u)) ≫ fR.v τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ U _hg hU d u₀ R _ φR xR fR ev k G τ hev hG hφ hpt
  classical
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hP⟩ := hU
  choose Pm h1 h2 h3 h4 _ using hP
  obtain ⟨h₀, -⟩ := hpt.self_of_nhds
  let L := EuclideanSpace.equiv (Fin d) ℂ
  let x : (Fin d → ℂ) → (U.X k).dom := fun b =>
    if h : G (L.symm b) ∈ (U.X k).dom then ⟨G (L.symm b), h⟩ else ⟨G u₀, h₀⟩
  have hxb : ∀ b (h : G (L.symm b) ∈ (U.X k).dom), x b = ⟨G (L.symm b), h⟩ := fun b h => dif_pos h
  let P : (Fin d → ℂ) → ((F.Di (ik k)).La →+ (Fin g → ℂ)) := fun b => Pm k (x b)
  let p : (Fin d → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b => GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x b))
  have hu : ∀ b, F.u (ik k) (P b) =
      p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    fun b => (h3 k (x b)).symm.trans (ptF_fst (U.un k (x b))).symm
  have hs : ∀ b, p b ≫ pullback.snd _ _ = spMap σ := fun b => ptF_snd (U.un k (x b))
  have hgood : ∀ᶠ u in 𝓝 u₀, G u ∈ (U.X k).dom ∧
      ∀ τ' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u :=
    (hpt.mono fun u hu => hu.1).and
      (eventually_all.2 fun τ' => eventually_all.2 fun a => eventually_all.2 fun b => hG τ' a b)
  obtain ⟨B₀, hB₀, hB₀o, hu₀⟩ := eventually_nhds_iff.1 hgood
  let B : Set (Fin d → ℂ) := L.symm ⁻¹' B₀
  have hBo : IsOpen B := hB₀o.preimage L.symm.continuous
  have hb₀ : L u₀ ∈ B := by
    show L.symm (L u₀) ∈ B₀
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hu₀
  have hPd : ∀ a, DifferentiableOn ℂ (fun b => P b a) B := fun a => differentiableOn_pi.2 fun j =>
    (TrueCx.TorHolo.differentiableOn_perFr (U.X k) (x := fun b => G (L.symm b)) (fun b hb => (hB₀ _ hb).1)
      (fun τ' a' c' b hb => (((hB₀ _ hb).2 τ' a' c').comp b L.symm.differentiableAt).differentiableWithinAt)
      _ _ _).congr fun b hb => by
        show Pm k (x b) a j = _
        rw [h1, hxb b (hB₀ _ hb).1]
  let ev' : (Fin d → ℂ) → (R →+* ℂ) := fun b => ev (L.symm b)
  let Ex : (Fin d → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left) := fun b z =>
    liftEx Z F (p b) (ik k) (P b) (hu b) z ≫ Z.m.φ
  let Wd : Fin (Dw.mult τ) → (Fin d → ℂ) → Fin g → ℂ := fun i b =>
    if h : ∃ w, IsDerivAt0 (Ex b) w (spMap (dualMap (ev' b)) ≫ fR.v τ i) then h.choose else 0
  have core : ∀ b (h : G (L.symm b) ∈ (U.X k).dom),
      (cxPt Z (U.un k ⟨G (L.symm b), h⟩)).1 ≫ genι Z = spMap (ev (L.symm b)) ≫ xR →
      (ev (L.symm b)).comp φR = σ → ∀ i,
      IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) ∧
      IsCombAtG Z.t ((cxPt Z (U.un k ⟨G (L.symm b), h⟩)).1 ≫ genι Z)
        ((cxFrame Z (U.un k ⟨G (L.symm b), h⟩)).v τ) (fun a => Wd i b (e.symm ⟨τ, a⟩))
        (spMap (dualMap (ev (L.symm b))) ≫ fR.v τ i) := by
    intro b h hx hφb i
    rw [← hxb b h] at hx ⊢
    obtain ⟨gF, hgF⟩ := HolFrames.exists_bc fR (ev (L.symm b)) (φ' := σ) hφb.symm hx
    have hxp : p b ≫ Z.jQ ≫ genι Z = (cxPt Z (U.un k (x b))).1 ≫ genι Z := (Category.assoc _ _ _).symm
    have hExp := isExpAt_pushEx E H Dw l Xo c O β Z g _ _ F (p b) (ik k) (P b) _ (hu b) rfl (h2 k (x b))
    have hδ : ∀ a, IsDerivAt0 (fun z => (pushEx Z F (p b) (ik k) (P b) _ (hu b) rfl z).left)
        (Pi.single (e.symm ⟨τ, a⟩) 1) ((cxFrame Z (U.un k (x b))).v τ a) := by
      intro a
      obtain ⟨w, hwt, hw0, hwm⟩ := EigFrame.ofFrPt_v Z (U.un k (x b))
        (x := (cxPt Z (U.un k (x b))).1 ≫ genι Z) (Category.assoc _ _ _).symm τ a
      have hw0' : (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left) ≫ Z.m0.toSABMap.φ = (U.un k (x b)).u τ a := hw0
      have hwm' : (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left) ≫ Z.m.φ = (cxFrame Z (U.un k (x b))).v τ a := hwm
      have hd : IsDerivAt0 (fun z => (F.ex (ik k) (P b) z).left) (Pi.single (e.symm ⟨τ, a⟩) 1)
          (w ≫ Z.m0.toSABMap.φ) := by
        exact (congrArg (IsDerivAt0 _ _) hw0').mpr (h4 k (x b) τ a)
      have := isDerivAt0_comp_hom (isDerivAt0_liftEx Z F (p b) (ik k) (P b) (h2 k (x b)) (hu b) hwt.1 hd) Z.m.φ
      exact (congrArg (IsDerivAt0 _ _) hwm').mp this
    have ht : IsTanAtG Z.t (p b ≫ Z.jQ ≫ genι Z) (gF.v τ i) := by
      rw [hxp]; exact gF.tan τ i
    have hex : ∃ w, IsDerivAt0 (Ex b) w (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      obtain ⟨w, hw, -⟩ := hExp.2.2 _ ht
      exact ⟨w, (hgF τ i) ▸ hw⟩
    have hW : IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      have e0 : Wd i b = hex.choose := dif_pos hex
      rw [e0]
      exact hex.choose_spec
    refine ⟨hW, ?_⟩
    obtain ⟨a, ha, hwa⟩ := exists_comb_of_exp hxp _ hExp (cxFrame Z (U.un k (x b))) τ _ hδ (gF.v τ i)
      (gF.tan τ i) (gF.eig τ i) (Wd i b) ((hgF τ i).symm ▸ hW)
    have hfa : (fun a' => Wd i b (e.symm ⟨τ, a'⟩)) = a := by
      funext a'
      rw [hwa]
      have hi : ∀ j j' : Fin (Dw.mult τ), e.symm ⟨τ, j⟩ = e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
      simp [Finset.sum_apply, Pi.single_apply, hi]
    rw [hfa, ← hgF τ i]
    exact ha
  have ht : Tendsto L.symm (𝓝 (L u₀)) (𝓝 u₀) := by
    simpa using L.symm.continuous.tendsto (L u₀)
  refine ⟨fun u a i => Wd i (L u) (e.symm ⟨τ, a⟩), fun a i => ?_, ?_⟩
  · have hev'' : ∀ t, ∀ᶠ b in 𝓝 (L u₀), DifferentiableAt ℂ (fun b => ev' b t) b := fun t => by
      filter_upwards [ht.eventually (hev t)] with b hb
      exact hb.comp b L.symm.differentiableAt
    have hW : ∀ᶠ b in 𝓝 (L u₀), IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      filter_upwards [ht.eventually hpt, ht.eventually hφ] with b ⟨h, hx⟩ hφb
      exact (core b h hx hφb i).1
    have hd := eventually_differentiableAt_dir Z σ F (ik k) hBo hu (fun b => h2 k (x b)) hPd hs (fR.v τ i) ev' hb₀
      hev'' (Wd i) hW
    filter_upwards [(L.continuous.tendsto u₀).eventually hd] with u hu
    exact (differentiableAt_pi.1 hu (e.symm ⟨τ, a⟩)).comp u L.differentiableAt
  · filter_upwards [hpt, hφ] with u ⟨h, hx⟩ hφu
    refine ⟨h, fun i => ?_⟩
    have c := core (L u)
    rw [ContinuousLinearEquiv.symm_apply_apply] at c
    exact (c h hx hφu i).2

end GlobalTheory.HolCoordEv
end
end

section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_eigenvector_coordinates_holomorphic_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (d : ℕ) (u₀ : V d) (R : Type) [CommRing R] (φR : c.F →+* R) (xR : Sp R ⟶ Z.X) (fR : EigFrame Z φR xR) (ev : V d → (R →+* ℂ)) (k : U.Comp) (G : V d → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) (τ : E →+* ℂ), (∀ t, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ev u t) u) → (∀ τ' a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → (∀ᶠ u in 𝓝 u₀, (ev u).comp φR = σ) → (∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, (cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z = spMap (ev u) ≫ xR) → ∃ M : V d → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => M u a b) u) ∧ ∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, ∀ i, IsCombAtG Z.t ((cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z) ((cxFrame Z (U.un k ⟨G u, h⟩)).v τ) (fun b => M u b i) (spMap (dualMap (ev u)) ≫ fR.v τ i) := by
  first | exact @GlobalTheory.HolCoordEv.coords_holomorphic | exact GlobalTheory.HolCoordEv.coords_holomorphic | (intros; apply GlobalTheory.HolCoordEv.coords_holomorphic <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open CategoryTheory.Limits

namespace GlobalTheory.ShFam.StalkSpread

open GlobalTheory.LieLocFrame (res res_sum res_res)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_isMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (X : Var F) (j : X.X ⟶ gen Z) (z : X.X) (φz : c.F →+* X.X.presheaf.stalk z) (fz : EigFrame Z φz (stalkPt X z ≫ j ≫ genι Z)) (W₀ : X.X.Opens), z ∈ W₀ → stalkPt X z ≫ j ≫ genStr Z = spMap φz → ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)) (hz : z ∈ W), W ≤ W₀ ∧ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genStr Z = spMap φ ∧ fW.IsMap (X.X.presheaf.germ W z hz).hom fz := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ X j z φz fz W₀ hz₀ hstr
  obtain ⟨U₀, hU₀, φ₀, f₀, hy₀, hs₀, -⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (j z)
  let gm₀ : Γ(gen Z, U₀) →+* X.X.presheaf.stalk z :=
    (X.X.presheaf.germ (j ⁻¹ᵁ U₀) z hy₀).hom.comp (j.app U₀).hom
  have hgm : ∀ (U : X.X.Opens) (hy : z ∈ U) (h : U ≤ j ⁻¹ᵁ U₀),
      (X.X.presheaf.germ U z hy).hom.comp (j.appLE U₀ U h).hom = gm₀ := fun U hy h =>
    RingHom.ext fun a => X.X.presheaf.germ_res_apply (homOfLE h) z hy _
  have hρ : ∀ (U : X.X.Opens) (hU : IsAffineOpen U) (h : U ≤ j ⁻¹ᵁ U₀),
      spMap (j.appLE U₀ U h).hom ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) =
        (show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j := fun U hU h =>
    IsAffineOpen.SpecMap_appLE_fromSpec j hU₀ hU h
  have hx₀ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) = stalkPt X z ≫ j := by
    obtain ⟨U, hU, hy, h⟩ := exists_isAffineOpen_mem_and_subset (X := X.X) (U := j ⁻¹ᵁ U₀) (x := z) hy₀
    rw [← hgm U hy h, ← spMap_comp_spMap, Category.assoc, hρ U hU h, ← Category.assoc, Spread.spMap_germ]
    rfl
  have hs₀' : (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genStr Z = spMap φ₀ := hs₀
  have hφ₀ : gm₀.comp φ₀ = φz := by
    have h1 : spMap (gm₀.comp φ₀) = spMap φz := by
      rw [← spMap_comp_spMap, ← hs₀', ← Category.assoc, hx₀, Category.assoc, hstr]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hx₁ : spMap gm₀ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      stalkPt X z ≫ j ≫ genι Z := by rw [← Category.assoc, hx₀, Category.assoc]
  obtain ⟨g, hg⟩ := Spread.exists_bc f₀ gm₀ hφ₀ hx₁
  choose A B hAB hA using Spread.exists_coord g fz
  obtain ⟨U, hU, hy, s, hle, hs⟩ := Spread.exists_affine_germs z (W := W₀ ⊓ j ⁻¹ᵁ U₀) ⟨hz₀, hy₀⟩
    (fun p : Bool × (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ)) =>
      (cond p.1 (A p.2.1) (B p.2.1)) p.2.2.1 p.2.2.2)
  have h₀ : U ≤ j ⁻¹ᵁ U₀ := fun w hw => (hle hw).2
  let gm : Γ(X.X, U) →+* X.X.presheaf.stalk z := (X.X.presheaf.germ U z hy).hom
  let ρ : Γ(gen Z, U₀) →+* Γ(X.X, U) := (j.appLE U₀ U h₀).hom
  let A' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(X.X, U) :=
    fun τ => Matrix.of fun i k => s (true, ⟨τ, i, k⟩)
  let B' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(X.X, U) :=
    fun τ => Matrix.of fun i k => s (false, ⟨τ, i, k⟩)
  have hA' : ∀ τ i k, gm (A' τ i k) = A τ i k := fun τ i k => hs (true, ⟨τ, i, k⟩)
  have hB' : ∀ τ i k, gm (B' τ i k) = B τ i k := fun τ i k => hs (false, ⟨τ, i, k⟩)
  have hAB' : ∀ τ, B' τ * A' τ = 1 := fun τ => Matrix.ext fun i k => germ_injective_of_isIntegral X.X z hy (by
    show gm _ = gm _
    have := congrFun (congrFun (hAB τ) i) k
    simp only [Matrix.mul_apply, map_sum, map_mul, hA', hB', Matrix.one_apply] at this ⊢
    rw [this]
    split_ifs <;> simp)
  have hx₂ : spMap ρ ≫ (show Sp Γ(gen Z, U₀) ⟶ gen Z from hU₀.fromSpec) ≫ genι Z =
      ((show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j) ≫ genι Z := by rw [← Category.assoc, hρ U hU h₀]
  have hx₃ : spMap gm ≫ ((show Sp Γ(X.X, U) ⟶ X.X from hU.fromSpec) ≫ j) ≫ genι Z =
      stalkPt X z ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, Spread.spMap_germ]
    rfl
  obtain ⟨g', hg'⟩ := Spread.exists_bc f₀ ρ rfl hx₂
  obtain ⟨fr, hfr⟩ := Spread.exists_change g' A' B' hAB'
  refine ⟨U, hU, ρ.comp φ₀, fr, hy, fun w hw => (hle hw).1, ?_, fun τ i => ?_⟩
  · rw [← hρ U hU h₀, Category.assoc, hs₀']
    exact spMap_comp_spMap φ₀ ρ
  · have hv : fz.vec τ i = res gm hx₃ (fr.vec τ i) := by
      rw [hfr, res_sum, hA]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hA', hg, hg', res_res ρ hx₂ gm hx₃ (hgm U hy h₀) hx₁]
    exact congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) hv

end GlobalTheory.ShFam.StalkSpread
end
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_spread_stalk_lieEigenspaceFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (X : Var F) (j : X.X ⟶ gen Z) (z : X.X) (φz : c.F →+* X.X.presheaf.stalk z) (fz : EigFrame Z φz (stalkPt X z ≫ j ≫ genι Z)) (W₀ : X.X.Opens), z ∈ W₀ → stalkPt X z ≫ j ≫ genStr Z = spMap φz → ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)) (hz : z ∈ W), W ≤ W₀ ∧ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genStr Z = spMap φ ∧ fW.IsMap (X.X.presheaf.germ W z hz).hom fz := by
  atlas_forward_decl GlobalTheory.ShFam.StalkSpread.exists_affine_isMap
end

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NearFrame

theorem dualMap_comp_near {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem exists_affine_frame_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), Tied e X j f₀ Eb A₀ → ∀ (y : CxPts X.str (σ.comp e.toRingHom)), ∀ A ∈ Eb.S (under y), ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)), y ∈ ptsIn X.str (σ.comp e.toRingHom) W ∧ ∀ y' (hy' : y' ∈ ptsIn X.str (σ.comp e.toRingHom) W), (evHom hy').comp φ = σ ∧ ∃ g : EigFrame Z σ ((cxOf e σ hj y').1 ≫ genι Z), FrameAt e f₀ A₀ A y' g ∧ fW.IsMap (evHom hy') g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ X j f₀ Eb A₀ hj hT y A hA
  obtain ⟨φz, fz, hx0, hφ0, hv0⟩ := hT.2 (under y) A hA
  have inj := IsFractionRing.injective (X.X.presheaf.stalk (under y)) X.X.functionField
  have hgen : spMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) ≫ stalkPt X (under y) = genericPt X :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes _)
  have hstr : stalkPt X (under y) ≫ j ≫ genStr Z = spMap φz := by
    obtain ⟨p, hp⟩ := Spec.map_surjective (stalkPt X (under y) ≫ j ≫ genStr Z)
    have h1 : (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp p.hom =
        (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp φz := by
      refine EigLoc.spMap_inj ?_
      rw [← hφ0, ← TieBase.genericPt_str e X j hj, TieBase.spMap_trans, ← hgen]
      show _ ≫ Spec.map p = _
      rw [hp]
      simp only [Category.assoc]
    have h2 : p.hom = φz := RingHom.ext fun a => inj (RingHom.congr_fun h1 a)
    rw [← hp, ← h2]
    rfl
  obtain ⟨W, hW, φ, fW, hz, -, hWstr, hmap⟩ := GlobalTheory.T.exists_affineOpen_spread_stalk_lieEigenspaceFrame E H Dw l Xo c O β Z F X j (under y) φz fz ⊤ trivial hstr
  have hgerm : spMap (X.X.presheaf.germ W (under y) hz).hom ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) =
      stalkPt X (under y) := hW.fromSpecStalk_eq_fromSpecStalk hz
  have hφz : φz = (X.X.presheaf.germ W (under y) hz).hom.comp φ := by
    refine EigLoc.spMap_inj ?_
    rw [TieBase.spMap_trans, ← hstr, ← hWstr, ← hgerm]
    simp only [Category.assoc]
  refine ⟨W, hW, φ, fW, mem_ptsIn.2 hz, fun y' hy' => ?_⟩
  have hz' : under y' ∈ W := mem_ptsIn.1 hy'
  have hp' : spMap (evHom hy') ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = y'.1 :=
    Points.specMap_valMap_fromSpec hW y'.1 hy'
  have ha : (evHom hy').comp φ = σ := by
    refine EigLoc.spMap_inj ?_
    rw [TieBase.spMap_trans, ← hWstr, ← (cxOf e σ hj y').2]
    show _ = (y'.1 ≫ j) ≫ genStr Z
    rw [← hp']
    simp only [Category.assoc]
  refine ⟨ha, ?_⟩
  obtain ⟨g, hg⟩ := EigFrame.exists_isMap fW (evHom hy') (φ' := σ) (x' := (cxOf e σ hj y').1 ≫ genι Z) ha.symm (by
    show (y'.1 ≫ j) ≫ genι Z = _
    rw [← hp']
    simp only [Category.assoc])
  refine ⟨g, ?_, hg⟩
  let germ' := (X.X.presheaf.germ W (under y') hz').hom
  let χ : X.X.presheaf.stalk (under y') →+* ℂ := (Scheme.stalkClosedPointTo (R := .of ℂ) y'.1).hom
  have hχ : χ.comp germ' = evHom hy' := by
    show _ = (Points.valMap y'.1 W hy').hom
    rw [← CommRingCat.hom_comp]
    congr 1
    rw [Scheme.germ_stalkClosedPointTo]
    rfl
  have hgerm' : spMap germ' ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = stalkPt X (under y') :=
    hW.fromSpecStalk_eq_fromSpecStalk hz'
  obtain ⟨fz', hfz'⟩ := EigFrame.exists_isMap fW germ' (φ' := germ'.comp φ)
    (x' := stalkPt X (under y') ≫ j ≫ genι Z) rfl (by rw [← hgerm']; simp only [Category.assoc])
  have hκ : (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField).comp germ' =
      (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp (X.X.presheaf.germ W (under y) hz).hom :=
    RingHom.ext fun a => (algebraMap_germ hz' a).trans (algebraMap_germ hz a).symm
  refine ⟨germ'.comp φ, fz', χ, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of ℂ) y'.1).symm, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hx0, ← hgerm, ← hgerm']
    simp only [← Category.assoc]
    rw [← TieBase.spMap_trans, ← TieBase.spMap_trans, hκ]
  · rw [hφ0, hφz, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hκ]
  · intro τ i
    have e : (fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField)) ≫ fz'.v τ k) =
        fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField)) ≫ fz.v τ k := by
      funext k
      rw [hfz' τ k, hmap τ k, ← Category.assoc, ← Category.assoc, ← TieBase.spMap_trans, ← TieBase.spMap_trans,
        ← dualMap_comp_near, ← dualMap_comp_near, hκ]
    rw [e]
    exact hv0 τ i
  · intro τ i
    rw [hg τ i, hfz' τ i, ← Category.assoc, ← TieBase.spMap_trans, ← dualMap_comp_near, hχ]

end GlobalTheory.NearFrame
end
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_lieEigenFrame_near_complexPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), Tied e X j f₀ Eb A₀ → ∀ (y : CxPts X.str (σ.comp e.toRingHom)), ∀ A ∈ Eb.S (under y), ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)), y ∈ ptsIn X.str (σ.comp e.toRingHom) W ∧ ∀ y' (hy' : y' ∈ ptsIn X.str (σ.comp e.toRingHom) W), (evHom hy').comp φ = σ ∧ ∃ g : EigFrame Z σ ((cxOf e σ hj y').1 ≫ genι Z), FrameAt e f₀ A₀ A y' g ∧ fW.IsMap (evHom hy') g := by
  atlas_forward_decl GlobalTheory.NearFrame.exists_affine_frame_near
end

section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem exists_holo_coord_frameAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ τ : GlobalTheory.AllWt.Psi H, ∀ (kU : U.Comp) (G : V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X kU).Ψ (Dw.p + Dw.q)), (∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, cxPt T.Z (U.un kU ⟨G u, h⟩) = cxOf e σ hj (c'.e.symm u)) → (∀ τ' a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → ∃ M : V X.dim → Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => M u a b) u) ∧ IsUnit (M (c'.e y)).det ∧ ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, (∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm u)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm u) g) ∧ ∀ (x : Sp ℂ ⟶ T.Z.X) (g : EigFrame T.Z σ x), FrameAt e f₀ A₀ A (c'.e.symm u) g → ∀ i, IsCombAtG T.Z.t ((cxPt T.Z (U.un kU ⟨G u, h⟩)).1 ≫ genι T.Z) ((cxFrame T.Z (U.un kU ⟨G u, h⟩)).v τ.1) (fun b => M u b i) (g.v τ.1 i) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hLie y _ c' hyc A hA τ kU G hF hG
  obtain ⟨-, -, hTd⟩ := hLie
  obtain ⟨W, hW, φ, fW, hyW, hnear⟩ := GlobalTheory.T.exists_affine_lieEigenFrame_near_complexPoint E H Dw l Xo c O β T.Z F e σ X j f₀ Eb A₀ hj hTd y A hA
  classical
  let ev : V X.dim → (Γ(X.X, W) →+* ℂ) := fun u =>
    if h : c'.e.symm u ∈ ptsIn X.str (σ.comp e.toRingHom) W then evHom h else evHom hyW
  have hev : ∀ u (h : c'.e.symm u ∈ ptsIn X.str (σ.comp e.toRingHom) W), ev u = evHom h := fun u h => dif_pos h
  set S : Set (V X.dim) := c'.e.target ∩ c'.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W with hSdef
  have hSo : IsOpen S := c'.e.continuousOn_symm.isOpen_inter_preimage c'.e.open_target (isOpen_ptsIn _)
  have hu0 : c'.e y ∈ S := ⟨c'.e.map_source hyc, by show c'.e.symm (c'.e y) ∈ ptsIn X.str (σ.comp e.toRingHom) W; rw [c'.e.left_inv hyc]; exact hyW⟩
  have hSn : ∀ᶠ u in 𝓝 (c'.e y), u ∈ S := hSo.mem_nhds hu0
  have hevd : ∀ t, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ev u t) u := by
    intro t
    filter_upwards [hSn] with u hu
    refine ((c'.holo W t).differentiableAt (hSo.mem_nhds hu)).congr_of_eventuallyEq ?_
    filter_upwards [hSo.mem_nhds hu] with v hv
    simp only [Function.comp_apply, hev v hv.2, ev_eq hv.2]
  have hφ : ∀ᶠ u in 𝓝 (c'.e y), (ev u).comp φ = σ := by
    filter_upwards [hSn] with u hu
    rw [hev u hu.2]; exact (hnear _ hu.2).1
  have hpt : ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, (cxPt T.Z (U.un kU ⟨G u, h⟩)).1 ≫ genι T.Z =
      spMap (ev u) ≫ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι T.Z := by
    filter_upwards [hSn, hF] with u hu ⟨h, hc⟩
    refine ⟨h, ?_⟩
    rw [hc, hev u hu.2]
    have := GlobalTheory.Points.specMap_valMap_fromSpec hW (c'.e.symm u).1 hu.2
    show (c'.e.symm u).1 ≫ j ≫ genι T.Z = _
    rw [← this]
    simp only [Category.assoc]
    rfl
  obtain ⟨M, hMd, hMc⟩ := GlobalTheory.T.algebraic_eigenvector_coordinates_holomorphic_uniformisation E H Dw l Xo c O β T.Z σ U hσ hU X.dim (c'.e y) Γ(X.X, W) φ _ fW ev kU G τ.1 hevd hG hφ hpt
  refine ⟨M, hMd, ?_, ?_⟩
  · obtain ⟨h0, hc0⟩ := hMc.self_of_nhds
    obtain ⟨h0', hF0⟩ := hF.self_of_nhds
    obtain ⟨-, g0, -, hm0⟩ := hnear _ hu0.2
    have hx : (cxOf e σ hj (c'.e.symm (c'.e y))).1 ≫ genι T.Z = (cxPt T.Z (U.un kU ⟨G (c'.e y), h0⟩)).1 ≫ genι T.Z := by
      rw [hF0]
    have key : ∀ {x x' : Sp ℂ ⟶ T.Z.X} (hx : x = x') (g : EigFrame T.Z σ x) (G' : EigFrame T.Z σ x')
        (N : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ),
        (∀ i, IsCombAtG T.Z.t x' (G'.v τ.1) (fun b => N b i) (g.v τ.1 i)) → IsUnit N.det := by
      intro x x' hx g G' N h
      subst hx
      rw [← EigFrame.co_eq (f := G') (g := g) h]
      exact EigFrame.isUnit_det_co _ _ _
    refine key hx g0 (cxFrame T.Z (U.un kU ⟨G (c'.e y), h0⟩)) (M (c'.e y)) fun i => ?_
    rw [hm0 τ.1 i, ← hev _ hu0.2]
    exact hc0 i
  · filter_upwards [hMc, hSn] with u ⟨h, hc⟩ hu
    obtain ⟨-, g0, hg0, hm0⟩ := hnear _ hu.2
    refine ⟨h, ⟨g0, hg0⟩, fun x g hg i => ?_⟩
    rw [GlobalTheory.T.complexPoint_stalkFrame_vectors_eq E H Dw l Xo c O β T.Z F e σ X j f₀ A₀ A _ _ _ g g0 hg hg0 τ.1 i, hm0 τ.1 i, ← hev _ hu.2]
    exact hc i

end GlobalTheory.LieBase
end
end
