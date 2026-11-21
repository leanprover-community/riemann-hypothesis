import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsOpenDet
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalPairSumGramBound
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsContraction
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsSumframe
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairSumFrameAtPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrameStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open scoped Matrix ComplexOrder

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem eig_coords {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty)
    (i : Fin FU.n) {P : (FU.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (FU.Di i) ty P) {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left} (hv : IsDerivAt0 (fun z => (FU.ex i P z).left) w v) (a : 𝓞 E) (cc : ℂ)
    (h : v ≫ (Xo.univ.t.act.act a).left = spMap (Tor.epsMul cc) ≫ v) (j : Fin g) : ty j (a : E) * w j = cc * w j := by
  obtain ⟨v₁, hv₁, -⟩ := (FU.ex_diff i P hP).1 (PullbackSections.ExpRows.tyD ty a w)
  have h1 := PullbackSections.ExpRows.isDerivAt0_comp_lin (PullbackSections.anHol FU i P hP) (PullbackSections.ExpRows.tyD ty a) hv₁
  have h2 := PullbackSections.ExpRows.isDerivAt0_comp_hom hv (Xo.univ.t.act.act a).left
  have hfun : (fun z => (FU.ex i P z).left ≫ (Xo.univ.t.act.act a).left) =
      fun z => (FU.ex i P (PullbackSections.ExpRows.tyD ty a z)).left := funext fun z => by
    rw [PullbackSections.ExpRows.tyD_apply, FU.ex_lin i P hP a z]
    rfl
  rw [hfun] at h2
  have h3 := PullbackSections.ExpRows.isDerivAt0_unique h1 h2
  have h4 := PullbackSections.ExpRows.isDerivAt0_smul hv cc
  rw [← h, ← h3] at h4
  exact congrFun (((FU.ex_diff i P hP).2 v₁ hv₁.1).unique hv₁ h4) j

theorem chart_periods {Xo : Moduli D l} {σ : KA l →+* ℂ} {n : ℕ} (C : BdryChart Xo σ n 0) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) {A : Type} (x : A → Fin C.g → C.R) :
    ∃ (i : Fin FU.n) (B : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ)))
      (W : A → (Fin n → ℂ) → Fin g → ℂ) (G : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ),
      IsOpen B ∧ 0 ∈ B ∧ B ⊆ Metric.ball 0 1 ∧ IsHolPeriods (FU.Di i) ty B P ∧
      (∀ a, DifferentiableOn ℂ (W a) B) ∧ ∀ u ∈ B, FU.u i (P u) = C.pt u ≫ C.k ∧
        ((G u).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (G u) z z).re) ∧
          ∀ x y, (hermForm (G u) (P u x) (P u y)).im = (FU.Di i).EF x y) ∧
        (∃ Hm, C.IsRiem u Hm ∧ ∀ a b, hermForm Hm (fun e => C.ψ u (x a e)) (fun e => C.ψ u (x b e)) =
          hermForm (G u) (W a u) (W b u)) ∧
        ∀ a (t : 𝓞 E) (cc : ℂ), (spMap (dualMap (C.ψ u)) ≫ (C.M.pt (x a)).left) ≫ (C.t.act.act t).left =
          spMap (Tor.epsMul cc) ≫ spMap (dualMap (C.ψ u)) ≫ (C.M.pt (x a)).left →
          ∀ j, ty j (t : E) * W a u j = cc * W a u j := by
  classical
  have hpu : ∀ ρ : ℝ, punct n 0 ρ = Metric.ball 0 ρ := fun ρ => by ext z; simp [punct]
  obtain ⟨ρ, hρ0, hρB, ⟨e⟩⟩ := GlobalTheory.T.exists_family_exponential_locally C.R C.t.G C.g n C.M (Metric.ball 0 1) C.ψ C.t.semi.smooth C.hol 0
    (Metric.mem_ball_self one_pos)
  have hy : IsHolTo (Metric.ball 0 ρ) fun u => C.pt u ≫ C.k :=
    GlobalTheory.LocLift.isHolTo_comp_hom (Marking.isHolTo_mono' (Marking.isHolTo_pt C)
      (by rw [hpu]; exact hρB) Metric.isOpen_ball) C.k
  obtain ⟨B', i, P₀, hB, h0, hsubB, hP, hu⟩ := FU.lift n (Metric.ball 0 ρ) _ Metric.isOpen_ball
    (fun b hb => by rw [Category.assoc]; exact (C.pt_eq b (by rw [hpu]; exact hρB hb)).2) hy 0
    (Metric.mem_ball_self hρ0)
  have hsub1 : B' ⊆ punct n 0 1 := by rw [hpu]; exact hsubB.trans hρB
  obtain ⟨r, Wt, hr⟩ := Marking.exists_family C FU i P₀ hsub1 hP hu ((1 : Over.mk (C.pt 0) ⟶ C.tV.G).left)
  have hol := Marking.family_hol C FU i P₀ hB hsub1 hP Wt
    (fun b hb x => ⟨((hr b hb).2.2.2.1 x).1, ((hr b hb).2.2.2.1 x).2.1⟩)
  have holr : IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (r bz.1 bz.2).left) :=
    GlobalTheory.FiniteOrderConst.isHolTo_of_eqOn (GlobalTheory.HolFibre.isHolTo_comp hol C.m₁.φ)
      fun bz hb => (((hr _ hb.1).2.2.2.1 _).2.2).symm
  obtain ⟨hl, hlhol, hl2⟩ := exists_linear_lift_of_additive_family C.R C.t.G C.g n C.M (Metric.ball 0 ρ) C.ψ e g B' r
    hB hsubB (fun b hb => (hr b hb).1) holr
  have hbij : ∀ z ∈ B', Function.Bijective (hl z) := by
    intro z hz
    obtain ⟨hadd, hons, hker, -, -⟩ := hr z hz
    obtain ⟨δ, hδ, hiso⟩ := Marking.isolated_of_isPeriod _ (hP.1 z hz)
    refine Marking.bijective_of_exp (e.ex z) (r z) (hl z) (e.add z (hsubB hz)) (hl2 z hz).1 hons
      ⟨δ, hδ, fun x hx h1 => hiso x hx ((hker x).1 h1)⟩ ?_
    obtain ⟨W, hW, hzW, ρ', hρ', hinj⟩ := ExpLift.ex_inj_near e (hsubB hz)
    refine ⟨ρ', hρ', fun y hy h1 => hinj z hzW y (mem_ball_zero_iff.2 hy) 0 (Metric.mem_ball_self hρ') ?_⟩
    rw [h1, ExpLift.ex_zero e (hsubB hz)]
  have hg : g = C.g := by simpa using (LinearEquiv.ofBijective (hl 0) (hbij 0 h0)).finrank_eq
  subst hg
  let hm : (Fin n → ℂ) → Matrix (Fin C.g) (Fin C.g) ℂ := fun z => LinearMap.toMatrix' (hl z)
  have hmh : HolM B' hm := fun a b => differentiableOn_pi.1 (hlhol (Pi.single b 1)) a
  have hmv : ∀ z y, hm z *ᵥ y = hl z y := fun z y => LinearMap.toMatrix'_mulVec _ _
  have hmd : ∀ z ∈ B', (hm z).det ≠ 0 := fun z hz h => by
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    exact hy0 ((hbij z hz).1 (by rw [← hmv, hy, map_zero]))
  let W : A → (Fin n → ℂ) → Fin C.g → ℂ := fun a z => (hm z)⁻¹ *ᵥ fun e => C.ψ z (x a e)
  have hW : ∀ z ∈ B', ∀ a, hl z (W a z) = fun e => C.ψ z (x a e) := fun z hz a => by
    rw [← hmv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ (hmd z hz)), Matrix.one_mulVec]
  choose! G hG using fun z (hz : z ∈ B') => (hP.1 z hz).2.2.2.2
  refine ⟨i, B', P₀, W, G, hB, h0, hsubB.trans hρB, hP, fun a => differentiableOn_pi.2 fun j => ?_,
    fun z hz => ⟨hu z hz, hG z hz, ?_, fun a t cc hc => ?_⟩⟩
  · simp only [W, Matrix.mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun k _ => (hmh.inv hmd j k).mul ((C.hol.2 _).mono (hsubB.trans hρB))
  · obtain ⟨-, -, -, hWz, -⟩ := hr z hz
    let hh : (Fin C.g → ℂ) ≃ₗ[ℂ] (Fin C.g → ℂ) := LinearEquiv.ofBijective (hl z) (hbij z hz)
    obtain ⟨Hm, -, hf⟩ := Marking.herm_transport (G z) hh (hG z hz).1
    refine ⟨Hm, Marking.isRiem_of_period C FU e i (hsubB hz) (hsub1 hz) (P₀ z) (hP.1 z hz) (hu z hz) (r z) (Wt z)
        (fun x => ⟨(hWz x).2.1, (hWz x).2.2⟩) hh (hl2 z hz).2.2 (G z) Hm (hG z hz).1 (hG z hz).2.2 hf, fun a b => ?_⟩
    rw [← hf, ← hW z hz, ← hW z hz]
    rfl
  · obtain ⟨-, -, -, hWz, -⟩ := hr z hz
    have hD : IsDerivAt0 (fun x => (r z x).left) (W a z) (spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x a)).left) := by
      rw [(hl2 z hz).2.2, hW z hz]
      exact Marking.isDerivAt0_frame e (hsubB hz) (x a)
    haveI := C.j_open
    haveI : IsOpenImmersion C.m₁.φ := MorphismProperty.of_isPullback C.m₁.cart.1.flip ‹IsOpenImmersion C.j›
    obtain ⟨v', hv1, hv2⟩ := Marking.deriv_of_open C.m₁.φ (Wt z) (W a z) _ (by
      have : (fun x => Wt z x ≫ C.m₁.φ) = fun x => (r z x).left := funext fun x => (hWz x).2.2
      rw [this]; exact hD)
    have h1 := PullbackSections.ExpRows.isDerivAt0_comp_hom hv2 C.m₂.φ
    have h2 : (fun x => Wt z x ≫ C.m₂.φ) = fun x => (FU.ex i (P₀ z) x).left := funext fun x => (hWz x).2.1
    rw [h2] at h1
    have h3 : v' ≫ (C.tV.act.act t).left = spMap (Tor.epsMul cc) ≫ v' := by
      rw [← cancel_mono C.m₁.φ, Category.assoc, Category.assoc, hv1, ← hc, ← hv1, Category.assoc]
      exact congrArg (v' ≫ ·) (C.m₁.act t)
    refine eig_coords FU i (hP.1 z hz) h1 t cc ?_
    rw [← Category.assoc, ← h3, Category.assoc, Category.assoc]
    exact congrArg (v' ≫ ·) (C.m₂.act t).symm

theorem exists_chart {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X' : Scheme.{0})
    (jx : X' ⟶ Y.X) (t : SAB H X') (m : SABMap t Y.t jx) (τ : c.F →+* ℂ) (n : ℕ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X'))
    (hp : IsHolTo (Metric.ball 0 1) p)
    (hs : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ jx ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)))
    (hpt : ∀ u ∈ Flat.punct n 0 1, ∀ x : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)),
      x ≫ pullback.fst _ _ = p u ≫ jx → Set.range x ⊆ Set.range Y.jQ) :
    ∃ (ρ : ℝ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n 0) (h : Sp C.R ⟶ X')
      (κ : C.V ⟶ Xo.XF c), 0 < ρ ∧ ρ ≤ 1 ∧ Nonempty (SABMap C.t t h) ∧ κ ≫ Y.j = C.j ≫ h ≫ jx ∧
      κ ≫ pullback.fst _ _ = C.k ∧
      ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ h = p ((ρ : ℂ) • z) := by
  classical
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  let fP := pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))
  let sZ := pullback.snd jx fP
  let fZ := pullback.fst jx fP
  let j := pullback.fst sZ Y.jQ
  let g := pullback.snd sZ Y.jQ
  have := Y.jQ_open
  have hj : IsOpenImmersion j := inferInstance
  let k : pullback sZ Y.jQ ⟶ Xo.X := g ≫ pullback.fst _ _

  obtain ⟨tZ, ⟨mZ⟩⟩ := exists_sab fZ t
  obtain ⟨tU, ⟨mU⟩⟩ := exists_sab g Y.oF.t
  obtain ⟨q₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m mZ
  obtain ⟨q₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m mU
  have e₁ : g ≫ Y.jQ ≫ fP = j ≫ fZ ≫ jx := by
    have a₁ : j ≫ sZ = g ≫ Y.jQ := pullback.condition
    have a₂ : fZ ≫ jx = sZ ≫ fP := pullback.condition
    rw [a₂, ← Category.assoc g, ← a₁, Category.assoc]
  rw [e₁] at q₂
  have q₁' : SABMap tZ Y.t (fZ ≫ jx) := q₁
  obtain ⟨mj, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel q₁' q₂
  obtain ⟨mk, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap mU

  let p' : (Fin n → ℂ) → (Sp ℂ ⟶ X') := fun u => if u ∈ Metric.ball (0 : Fin n → ℂ) 1 then p u else p 0
  have hp'e : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u = p u := fun u hu => if_pos hu
  have hp' : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) p' := GlobalTheory.LocLift.isHolTo_congr hp hp'e
  have hs' : ∀ u, (p' u ≫ jx) ≫ Y.s = spMap τ ≫ spMap (algebraMap (𝓞 c.F) c.F) := fun u => by
    have : p' u ≫ jx ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) := by
      by_cases hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1
      · rw [hp'e u hu]; exact hs u hu
      · simp only [p', if_neg hu]; simpa [h0] using hs 0 h0
    rw [Category.assoc, this]
    simp [spMap]
  let q : (Fin n → ℂ) → (Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    fun u => pullback.lift (p' u ≫ jx) (spMap τ) (hs' u)
  have hq : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) q :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.holPair _ _ _ Y.s (spMap (algebraMap (𝓞 c.F) c.F)) n _ _ _ hs' Metric.isOpen_ball
      (GlobalTheory.LocLift.isHolTo_comp_hom hp' jx) (GlobalTheory.PeriodTests.isHolTo_const Metric.isOpen_ball _)
  have hc : ∀ u, p' u ≫ jx = q u ≫ fP := fun u => (pullback.lift_fst _ _ _).symm
  let y : (Fin n → ℂ) → (Sp ℂ ⟶ pullback jx fP) := fun u => pullback.lift (p' u) (q u) (hc u)
  have hy : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) y :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.holPair _ _ _ jx fP n _ _ _ hc Metric.isOpen_ball hp' hq
  have hpu : ∀ z ∈ Flat.punct n 0 1, ∃ w : Sp ℂ ⟶ pullback sZ Y.jQ, w ≫ j = y z ∧
      w ≫ k ≫ Xo.s = spMap (τ.comp (IntermediateField.inclusion c.le).toRingHom) := fun z hz => by
    have hr : Set.range (q z) ⊆ Set.range Y.jQ :=
      hpt z hz (q z) ((pullback.lift_fst _ _ _).trans (by rw [hp'e z hz.1]))
    let w₀ := IsOpenImmersion.lift Y.jQ (q z) hr
    have hw₀ : w₀ ≫ Y.jQ = q z := IsOpenImmersion.lift_fac _ _ _
    have hys : y z ≫ sZ = w₀ ≫ Y.jQ := (pullback.lift_snd _ _ _).trans hw₀.symm
    refine ⟨pullback.lift (y z) w₀ hys, pullback.lift_fst _ _ _, ?_⟩
    have h₁ : pullback.lift (y z) w₀ hys ≫ k = w₀ ≫ pullback.fst _ _ := by
      simp only [k, g]; rw [pullback.lift_snd_assoc]
    rw [← Category.assoc, h₁, Category.assoc, pullback.condition, ← Category.assoc]
    have h₂ : w₀ ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = spMap τ := by
      rw [← Y.jQ_over, ← Category.assoc, hw₀]
      exact pullback.lift_snd _ _ _
    rw [h₂]
    simp [spMap]
  obtain ⟨ρ, C, i, e, hρ, hρ1, -, ⟨mi⟩, hej, hek, hψ⟩ :=
    Flat.exists_bdryChart_of_hol E H D l Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) _ tZ _ j k tU n 0 y
      (Nat.zero_le _) hj ⟨mj⟩ ⟨mk⟩ hy hpu
  obtain ⟨mh, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mZ mi
  refine ⟨ρ, C, i ≫ fZ, e ≫ g, hρ, hρ1, ⟨mh⟩, ?_, (Category.assoc _ _ _).trans hek, fun z hz => ?_⟩
  · have e₂ : g ≫ Y.j = j ≫ fZ ≫ jx := e₁
    rw [Category.assoc, e₂, ← Category.assoc, hej, Category.assoc, Category.assoc]
  have hin : (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith [norm_nonneg z]
  rw [← Category.assoc, hψ z hz, ← hp'e _ hin]
  exact pullback.lift_fst _ _ _

end PositivityTheory.Xgp.c_bm_exists_period
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

open GlobalTheory GlobalTheory.FibreDeriv GlobalTheory.VerticalDeriv

theorem exists_isDerivAt0_loc {g : ℕ} {Z : Scheme.{0}} {B : Set (Fin g → ℂ)} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)}
    (hol : IsHolTo B e) (hB : 0 ∈ B) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber ℂ) ⟶ Z, IsDerivAt0 e w v := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have hd := LocalLift.hol_differentiableAt hol hB h0
  let J : Γ(Z, U) →+* DualNumber ℂ :=
    { toFun := fun f => jet w (fun z => valAt' (e z) U f)
      map_one' := by
        have : (fun z => valAt' (e z) U 1) =ᶠ[nhds 0] fun _ => 1 := by
          filter_upwards [LocalLift.hol_eventually_mem hol hB h0] with z hz
          exact valAt'_one _ hz.2
        rw [jet_congr w this, jet_const, map_one]
      map_zero' := by
        simp only [valAt'_zero]
        rw [jet_const, map_zero]
      map_add' := fun f f' => by
        simp only [valAt'_add]
        exact jet_add w (hd f) (hd f')
      map_mul' := fun f f' => by
        simp only [valAt'_mul]
        exact jet_mul w (hd f) (hd f') }
  obtain ⟨v, hv, hve⟩ := TangentOrigin.exists_evalPt_eq hU J
  refine ⟨v, isDerivAt0_of_affine ?_ hU hv fun a => ⟨hd a, DFunLike.congr_fun hve a⟩⟩
  refine TangentOrigin.ext_evalPt hU ((TangentOrigin.top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)
  refine (TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC v U hv _ f).trans ?_
  rw [hve, ← TangentOrigin.valAt'_eq_evalPt]
  exact fst_jet w (fun z => valAt' (e z) U f)

end PositivityTheory.Xgp.c_bm_exists_period
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open scoped Matrix ComplexOrder

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

theorem valAt_cst {X : Scheme.{0}} {Ω O R : Type} [Field Ω] [CommRing O] [CommRing R] [IsLocalRing R]
    {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} (h : genPt ξ ⤳ centre z) (q : X ⟶ Sp O) {α : O →+* Ω} {β : O →+* R}
    (hα : ξ ≫ q = spMap α) (hβ : z ≫ q = spMap β) (a : O) : ValAt ξ z (α a) (β a) := by
  let gm := Spec.preimage (X.fromSpecStalk (centre z) ≫ q)
  have hgm : Spec.map gm = X.fromSpecStalk (centre z) ≫ q := Spec.map_preimage _
  refine ⟨h, gm.hom a, ?_, ?_⟩
  · have e : Spec.map (CommRingCat.ofHom ((genMap ξ (⟨centre z, h⟩ : Cpt ξ)).comp gm.hom)) = spMap α := by
      calc Spec.map (CommRingCat.ofHom ((genMap ξ (⟨centre z, h⟩ : Cpt ξ)).comp gm.hom))
          = Spec.map (CommRingCat.ofHom (genMap ξ (⟨centre z, h⟩ : Cpt ξ))) ≫ Spec.map gm := Spec.map_comp gm _
        _ = ξ ≫ q := by
          rw [hgm, ← Category.assoc]
          exact congrArg (· ≫ q) (LieTangent.spec_genMap ξ _)
        _ = spMap α := hα
    have := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    exact DFunLike.congr_fun this a
  · have e : Spec.map (CommRingCat.ofHom ((Scheme.stalkClosedPointTo z).hom.comp gm.hom)) = spMap β := by
      calc Spec.map (CommRingCat.ofHom ((Scheme.stalkClosedPointTo z).hom.comp gm.hom))
          = Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo z).hom) ≫ Spec.map gm := Spec.map_comp gm _
        _ = z ≫ q := by
          erw [hgm, ← Category.assoc]
          exact congrArg (· ≫ q) (LieTangent.spec_centre z)
        _ = spMap β := hβ
    have := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    exact DFunLike.congr_fun this a

theorem lieValAt_end {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
    {V : Type} [AddCommGroup V] [Module Ω V] {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {f : G ⟶ G} [IsMonHom f] {A : V →ₗ[Ω] V} (hA : M.IsDiffOf f A) {e : V}
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z (A e) (w ≫ f) := by
  obtain ⟨hc, v, ⟨h1, h2⟩, h3⟩ := h
  refine ⟨hc, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · unfold IsTanAt at h1 ⊢
    rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]
  · rw [hA e, Over.comp_left, Over.comp_left, h2]
    exact Category.assoc _ _ _
  · rw [Over.comp_left, Over.comp_left, h3]
    exact Category.assoc _ _ _

theorem isDerivAt0_congr {g : ℕ} {X : Scheme.{0}} {e e' : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt0 e w v) (he : ∀ᶠ z in nhds 0, e' z = e z) : IsDerivAt0 e' w v := by
  refine ⟨h.1.trans he.self_of_nhds.symm, fun U hU f => (h.2 U hU f).trans ?_⟩
  have : (fun z => valAt' (e' z) U f) =ᶠ[nhds 0] fun z => valAt' (e z) U f := he.mono fun z hz => by simp only [hz]
  rw [this.fderiv_eq]

theorem hom_dual_const {F : Type} [Field F] [NumberField F] (δ : F →+* DualNumber ℂ) :
    δ = (algebraMap ℂ (DualNumber ℂ)).comp ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp δ) := by
  have hu : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  have h := Algebra.FormallyUnramified.ext' (R := ℚ) (A := F) (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
    ⟨2, by
      rw [Submodule.zero_eq_bot, eq_bot_iff, sq, Ideal.mul_le]
      intro a ha b hb
      have ha' : a.fst = 0 := ha
      have hb' : b.fst = 0 := hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha', hb']⟩
    δ.toRatAlgHom ((algebraMap ℂ (DualNumber ℂ)).comp ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp δ)).toRatAlgHom
    (fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  exact RingHom.ext fun x => DFunLike.congr_fun h x

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem model_periods {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
    {A : Type} [Fintype A] (b : A → 𝔐.Li) {n : ℕ} (p : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (τ : c.F →+* ℂ)
    {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (hp : IsHolTo (Metric.ball 0 1) p)
    (hc : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)))
    (hi : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.Interior (p u))
    (hlat : ∀ a, b a ∈ 𝔐.M.lat ⟨centre (p 0), 𝔐.all _⟩) :
    ∃ (i : Fin FU.n) (ρ : ℝ) (B : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ)))
      (W : A → (Fin n → ℂ) → Fin g → ℂ) (G : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), 0 < ρ ∧ ρ ≤ 1 ∧
      IsOpen B ∧ 0 ∈ B ∧ B ⊆ Metric.ball 0 1 ∧ IsHolPeriods (FU.Di i) ty B P ∧
      (∀ a, DifferentiableOn ℂ (W a) B) ∧ (∀ u ∈ B,
        ((G u).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (G u) z z).re) ∧
          ∀ x y, (hermForm (G u) (P u x) (P u y)).im = (FU.Di i).EF x y) ∧
        (∀ (r : ℕ) (f : Fin r → A), 𝔐.M.GramAt 𝔐.t.PP.L (p ((ρ : ℂ) • u)) (fun k => b (f k))
          (Matrix.of fun i j => (Real.pi : ℂ) * hermForm (G u) (W (f j) u) (W (f i) u))) ∧
        ∀ a s, b a ∈ 𝔐.Vgen s → ∀ (t : 𝓞 E) j, ty j (t : E) * W a u j = τ (labelEmb c s t) * W a u j) ∧
      ∀ v, (∀ (U : Xo.X.Opens) (f : Γ(Xo.X, U)), ⊤ ≤ FU.u i (P 0) ⁻¹ᵁ U →
          fderiv ℂ (fun u => valAt' (FU.u i (P u)) U f) 0 v = 0) →
        ∃ V : Sp (DualNumber ℂ) ⟶ 𝔐.X, IsDerivAt0 (fun u => p ((ρ : ℂ) • u)) v V ∧
          V ≫ 𝔐.f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0 ≫ 𝔐.f := by
  classical
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  let ea := Fintype.equivFin A
  obtain ⟨W, hW, v, hq, htan, hval⟩ := GlobalTheory.T.lattice_tangent_vectors_affine_open 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ⟨centre (p 0), 𝔐.all _⟩ _
    (fun k => b (ea.symm k)) 𝔐.tie.gen (fun k => hlat _)
  have hW0 : ⊤ ≤ p 0 ⁻¹ᵁ W := fun x _ => by
    have : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst this
    exact hq
  obtain ⟨ρ₁, ψ, hρ₁, hρ₁', hψ, hψp⟩ := GlobalTheory.T.holomorphic_disc_in_affine_open 𝔐.X W hW n p hp hW0
  have hp₁ : IsHolTo (Metric.ball 0 1) (fun u => spMap (ψ u)) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_spMap Metric.isOpen_ball hψ.2
  obtain ⟨tW, ⟨mW⟩⟩ := exists_sab hW.fromSpec 𝔐.t
  obtain ⟨mY, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp 𝔐.m mW
  obtain ⟨ρ₂, C, h, κ, hρ₂, hρ₂', ⟨mC⟩, hκ₁, hκ₂, hC⟩ := exists_chart Y _ (hW.fromSpec ≫ 𝔐.f) tW mY τ n
    (fun u => spMap (ψ u)) hp₁
    (fun u hu => by
      have := hc _ (FramePeriods.smul_mem_ball' hρ₁ hρ₁' hu)
      rw [← hψp u hu] at this
      simpa using this)
    (fun u hu x hx => FramePeriods.interior_range 𝔐 _ (hi _ (FramePeriods.smul_mem_ball' hρ₁ hρ₁' hu.1)) x (by
      rw [hx, ← hψp u hu.1, Category.assoc]))
  obtain ⟨θ, hθ⟩ : ∃ θ : Γ(𝔐.X, W) →+* C.R, spMap θ = h := ⟨(Spec.preimage h).hom, Spec.map_preimage _⟩
  subst hθ
  obtain ⟨mX, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mW mC
  obtain ⟨x, hx⟩ := GlobalTheory.T.abelian_map_tangent_coordinates E H 𝔐.X 𝔐.t Γ(𝔐.X, W) hW.fromSpec _ v C.R C.t θ mX C.g C.M htan
  have hw : ∀ z : Fin n → ℂ, ∃ w : A → (epsAt (spMap (C.ψ z) ≫ spMap θ ≫ hW.fromSpec) ⟶ 𝔐.t.G),
      (∀ k, 𝔐.M.ValAt _ (b k) (w k)) ∧
      ∀ k, (w k).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x (ea k))).left ≫ mX.φ := fun z => by
    have e : spMap ((C.ψ z).comp θ) ≫ hW.fromSpec = spMap (C.ψ z) ≫ spMap θ ≫ hW.fromSpec := by
      rw [← Category.assoc]; congr 1; exact Spec.map_comp _ _
    choose w hw1 hw2 using hval ((C.ψ z).comp θ) _ e (𝔐.all _)
    refine ⟨fun k => w (ea k), fun k => by simpa using hw1 (ea k), fun k => ?_⟩
    rw [hw2, FramePeriods.dualMap_comp', hx, Category.assoc]
  have hpt : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ spMap θ ≫ hW.fromSpec =
      p (((ρ₁ * ρ₂ : ℝ) : ℂ) • z) := fun z hz => by
    rw [← Category.assoc, hC z hz, hψp _ (FramePeriods.smul_mem_ball' hρ₂ hρ₂' hz), smul_smul]
    push_cast
    rfl
  have hρ : 0 < ρ₁ * ρ₂ := mul_pos hρ₁ hρ₂
  have hρ' : ρ₁ * ρ₂ ≤ 1 := mul_le_one₀ hρ₁' hρ₂.le hρ₂'
  obtain ⟨i, B, P, Wv, G, hB, h0, hsub, hP, hWv, hall⟩ := chart_periods C FU fun a => x (ea a)
  have hpu : punct n 0 1 = Metric.ball 0 1 := by ext z; simp [punct]
  refine ⟨i, ρ₁ * ρ₂, B, P, Wv, G, hρ, hρ', hB, h0, hsub, hP, hWv, fun u hu => ⟨(hall u hu).2.1, fun r f => ?_,
    fun a s hs t => ?_⟩, fun v hv => ?_⟩
  · obtain ⟨Hm, hR, hH⟩ := (hall u hu).2.2.1
    obtain ⟨w, hw1, hw2⟩ := hw u
    have hg := GlobalTheory.T.chart_lattice_tangent_coordinates E H D l Xo _ n 0 C 𝔐.X 𝔐.t _ mX Ω 𝔐.ξ 𝔐.Li 𝔐.M r (fun k => b (f k))
      (fun k => x (ea (f k))) u Hm (fun k => w (f k)) hR (fun k => hw1 _) (fun k => hw2 _)
    rw [← hpt u (hsub hu)]
    convert hg using 4 with _ i' _ j'
    rw [← hH]
    rfl
  · obtain ⟨w, hw1, hw2⟩ := hw u
    refine (hall u hu).2.2.2 a t _ ?_
    have hint : _root_.IsIntegral ℤ (labelEmb c s t) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ) t).map (labelEmb c s).toIntAlgHom
    obtain ⟨h1, st, hst, hst'⟩ := valAt_cst (z := spMap (C.ψ u) ≫ spMap θ ≫ hW.fromSpec) (𝔐.all _) (𝔐.f ≫ Y.s)
      𝔐.cst_over (by
        rw [hpt u (hsub hu)]
        exact hc _ (FramePeriods.smul_mem_ball' hρ hρ' (hsub hu))) ⟨_, hint⟩
    have h2 := (hw1 a).smul h1 st
    haveI := 𝔐.t.act.hom t
    have h3 := lieValAt_end (𝔐.act t) (hw1 a)
    have h4 : 𝔐.ρ t (b a) = 𝔐.emb s t • b a := sub_eq_zero.1 ((Submodule.mem_iInf _).1 hs t)
    have h5 : genMap 𝔐.ξ ⟨_, h1⟩ st = 𝔐.emb s t := hst
    have h6 : (Scheme.stalkClosedPointTo (spMap (C.ψ u) ≫ spMap θ ≫ hW.fromSpec)).hom st =
      τ (labelEmb c s t) := hst'
    rw [h5, ← h4, h6] at h2
    have h7 := congrArg CommaMorphism.left (h3.unique 𝔐.tie.gen h2)
    obtain ⟨vv, hvv⟩ := RiemGram.exists_value C.M (C.ψ u) (x (ea a))
    rw [← hvv]
    have h8 : (w a).left = vv.left ≫ mX.φ := by rw [hw2, hvv, Category.assoc]
    refine mX.cart.1.hom_ext ?_ ?_
    · have h9 : (w a).left ≫ (𝔐.t.act.act t).left = spMap (Tor.epsMul (τ (labelEmb c s t))) ≫ (w a).left := h7
      rw [h8, Category.assoc] at h9
      rw [Category.assoc, Category.assoc]
      exact (congrArg (vv.left ≫ ·) (mX.act t)).trans h9
    · exact (Over.w (vv ≫ C.t.act.act t)).trans (Over.w (LieTangent.epsScale _ (τ (labelEmb c s t)) ≫ vv)).symm
  · have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
    obtain ⟨v', hv'⟩ := exists_isDerivAt0_loc (Marking.isHolTo_pt C) (hpu ▸ hb0) v
    have hn : B ∈ nhds (0 : Fin n → ℂ) := hB.mem_nhds h0
    have hpj : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, C.pt u ≫ C.j ≫ spMap θ ≫ hW.fromSpec =
        p (((ρ₁ * ρ₂ : ℝ) : ℂ) • u) := fun u hu => by
      rw [← Category.assoc, (C.pt_eq u (hpu ▸ hu)).1, hpt u hu]
    refine ⟨v' ≫ C.j ≫ spMap θ ≫ hW.fromSpec, isDerivAt0_congr (PullbackSections.ExpRows.isDerivAt0_comp_hom hv' _)
      (Filter.eventually_of_mem hn fun u hu => (hpj u (hsub hu)).symm), ?_⟩
    have h1 : IsDerivAt0 (fun u => FU.u i (P u)) v (v' ≫ C.k) :=
      isDerivAt0_congr (PullbackSections.ExpRows.isDerivAt0_comp_hom hv' _)
        (Filter.eventually_of_mem hn fun u hu => (hall u hu).1)
    have h2 := PullbackSections.ExpRows.isDerivAt0_unique h1 (GlobalTheory.LocalLift.isDerivAt0_const _ v hv)
    have h3 : v' ≫ κ = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ C.pt 0 ≫ κ := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, hκ₂]
        rw [h2, (hall 0 h0).1]
      · obtain ⟨δ, hδ⟩ : ∃ δ : c.F →+* DualNumber ℂ, spMap δ = v' ≫ κ ≫ pullback.snd _ _ :=
          ⟨(Spec.preimage (v' ≫ κ ≫ pullback.snd _ _)).hom, Spec.map_preimage _⟩
        haveI : FiniteDimensional ℚ c.F := c.fin
        haveI : NumberField c.F := ⟨⟩
        have h4 : C.pt 0 = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' := hv'.1.symm
        simp only [Category.assoc, h4, ← hδ]
        conv_lhs => rw [hom_dual_const δ]
        simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    have h5 := hpj 0 hb0
    rw [smul_zero] at h5
    have h6 : C.j ≫ spMap θ ≫ hW.fromSpec ≫ 𝔐.f = κ ≫ Y.j := hκ₁.symm
    rw [← h5]
    simp only [Category.assoc, h6]
    rw [← Category.assoc, h3]
    simp only [Category.assoc]

end PositivityTheory.Xgp.c_bm_exists_period
end
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_period

theorem det_head {p q k : ℕ} {I : Type} [Fintype I] [DecidableEq I] (M : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)
    (f : I → Fin q ⊕ Fin p) (hf : Function.Injective f)
    (hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x) :
    (M.submatrix (Subtype.val : {a : Fin (p + q) // (a : ℕ) < k} → _) Subtype.val).det =
      ((M.submatrix (blockEquiv p q) (blockEquiv p q)).submatrix f f).det := by
  let e : I ≃ {a : Fin (p + q) // (a : ℕ) < k} := Equiv.ofBijective
    (fun i => ⟨blockEquiv p q (f i), (hr _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j h => hf ((blockEquiv p q).injective (congrArg Subtype.val h)), fun ⟨a, ha⟩ => by
      obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
      obtain ⟨i, rfl⟩ := (hr x).1 ha
      exact ⟨i, rfl⟩⟩
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem sub_conj {m I : Type} [Fintype m] (H Y : Matrix m m ℂ) (f : I → m) :
    (Hᴴ * Y * H).submatrix f f = (H.submatrix id f)ᴴ * Y * H.submatrix id f := by
  ext a b
  simp [Matrix.mul_apply]

theorem periodGram_of {p q : ℕ} (Pi : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (Go : Matrix (Fin q) (Fin q) ℂ)
    (Gw : Matrix (Fin p) (Fin p) ℂ) (Z : Matrix (Fin q) (Fin p) ℂ) (hGo : Go.PosDef) (hdet : IsUnit Pi.det)
    (h : (gramOf (sigForm (p + q) p) Pi).submatrix (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) :
    IsPeriodGram p Pi ((fromBlocks Go 0 0 Gw).submatrix (blockEquiv p q).symm (blockEquiv p q).symm) := by
  classical
  refine ⟨⟨hdet, ?_⟩, fun h' hb k => ?_⟩
  · let f : {a : Fin (p + q) // (a : ℕ) < p + q - p} → Fin q := fun a => ⟨a.1, by have := a.2; omega⟩
    have hf : Function.Injective f := fun a b e => Subtype.ext (Fin.ext (congrArg Fin.val e :))
    convert hGo.submatrix hf using 1
    ext a b
    have := congrFun (congrFun h (.inl (f a))) (.inl (f b))
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply] at this
    simp at this
    simp only [gramHead, Matrix.neg_apply, Matrix.submatrix_apply]
    rw [neg_eq_iff_eq_neg]
    exact this
  have e1 : (gramOf (sigForm (p + q) p) (Pi * h')).submatrix (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks (omBlock h') 0 0 (wBlock h'))ᴴ *
        ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) *
        fromBlocks (omBlock h') 0 0 (wBlock h') := by
    rw [← h, ← hb.eq_fromBlocks, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    simp only [gramOf, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e2 : (h'ᴴ * (fromBlocks Go 0 0 Gw).submatrix (blockEquiv p q).symm (blockEquiv p q).symm * h').submatrix
      (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks (omBlock h') 0 0 (wBlock h'))ᴴ * fromBlocks Go 0 0 Gw * fromBlocks (omBlock h') 0 0 (wBlock h') := by
    rw [← hb.eq_fromBlocks, Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv p q),
      ← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv p q)]
    simp
  unfold gramHead
  by_cases hk : q ≤ k
  · let f : Fin q ⊕ {b : Fin p // q + (b : ℕ) < k} → Fin q ⊕ Fin p := Sum.map id Subtype.val
    have hf : Function.Injective f := Sum.map_injective.2 ⟨Function.injective_id, Subtype.val_injective⟩
    have hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x := by
      rintro (a | b)
      · exact ⟨fun _ => ⟨.inl a, rfl⟩, fun _ => by show (a : ℕ) < k; omega⟩
      · refine ⟨fun h => ⟨.inr ⟨b, h⟩, rfl⟩, ?_⟩
        rintro ⟨a | a, ha⟩
        · simp [f] at ha
        · obtain rfl : a.1 = b := by simpa [f] using ha
          exact a.2
    rw [det_head _ f hf hr, det_head _ f hf hr, e1, e2, sub_conj, sub_conj]
    set h₂ : Matrix (Fin p) {b : Fin p // q + (b : ℕ) < k} ℂ := (wBlock h').submatrix id Subtype.val
    have e3 : (fromBlocks (omBlock h') 0 0 (wBlock h')).submatrix id f = fromBlocks (omBlock h') 0 0 h₂ := by
      ext (a | a) (b | b) <;> rfl
    rw [e3]
    have e4 : (fromBlocks (omBlock h') 0 0 h₂)ᴴ *
        ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) * fromBlocks (omBlock h') 0 0 h₂ =
        (fromBlocks (omBlock h') (Z * h₂) 0 1)ᴴ * fromBlocks (-Go) 0 0 (h₂ᴴ * Gw * h₂) *
          fromBlocks (omBlock h') (Z * h₂) 0 1 := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply]
      simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    have e5 : (fromBlocks (omBlock h') 0 0 h₂)ᴴ * fromBlocks Go 0 0 Gw * fromBlocks (omBlock h') 0 0 h₂ =
        (fromBlocks (omBlock h') 0 0 1)ᴴ * fromBlocks Go 0 0 (h₂ᴴ * Gw * h₂) * fromBlocks (omBlock h') 0 0 1 := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply]
      simp [Matrix.mul_assoc]
    rw [e4, e5]
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg, norm_mul,
      norm_pow, norm_neg, norm_one, one_pow, one_mul]
  · let f : {a : Fin q // (a : ℕ) < k} → Fin q ⊕ Fin p := fun a => .inl a.1
    have hf : Function.Injective f := fun a b e => Subtype.ext (Sum.inl_injective e)
    have hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x := by
      rintro (a | b)
      · refine ⟨fun h => ⟨⟨a, h⟩, rfl⟩, ?_⟩
        rintro ⟨b, hb⟩
        obtain rfl : b.1 = a := Sum.inl_injective hb
        exact b.2
      · refine ⟨fun h => absurd h (by show ¬ q + (b : ℕ) < k; omega), ?_⟩
        rintro ⟨a, ha⟩
        simp [f] at ha
    rw [det_head _ f hf hr, det_head _ f hf hr, e1, e2, sub_conj, sub_conj]
    set h₁ : Matrix (Fin q) {a : Fin q // (a : ℕ) < k} ℂ := (omBlock h').submatrix id Subtype.val
    set O : Matrix (Fin p) {a : Fin q // (a : ℕ) < k} ℂ := 0 with hO
    have e3 : (fromBlocks (omBlock h') 0 0 (wBlock h')).submatrix id f = fromRows h₁ O := by
      ext (a | a) b <;> rfl
    rw [e3]
    have e4 : (fromRows h₁ O)ᴴ * ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) *
        fromRows h₁ O = -((fromRows h₁ O)ᴴ * fromBlocks Go 0 0 Gw * fromRows h₁ O) := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_fromRows_eq_fromCols_conjTranspose,
        fromCols_mul_fromBlocks, fromCols_mul_fromRows]
      simp [hO]
    rw [e4, Matrix.det_neg]
    simp

theorem periodGram_conj {N j : ℕ} {Pi G : Matrix (Fin N) (Fin N) ℂ} (h : IsPeriodGram j Pi G) :
    IsPeriodGram j (Pi.map (starRingEnd ℂ)) (G.map (starRingEnd ℂ)) := by
  classical
  have g : ∀ (k : ℕ) (X : Matrix (Fin N) (Fin N) ℂ), gramHead (sigForm N j) k (X.map (starRingEnd ℂ)) =
      (gramHead (sigForm N j) k X).map (starRingEnd ℂ) := fun k X => by
    ext a b
    simp [gramHead, gramOf, Matrix.mul_apply, Matrix.diagonal_apply, apply_ite]
  have dm : ∀ {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ),
      (X.map (starRingEnd ℂ)).det = starRingEnd ℂ X.det := fun X => (RingHom.map_det _ X).symm
  refine ⟨⟨?_, ?_⟩, fun h' hb k => ?_⟩
  · rw [dm]; exact h.1.1.map _
  · rw [g]
    suffices e : -(gramHead (sigForm N j) (N - j) Pi).map (starRingEnd ℂ) = (-gramHead (sigForm N j) (N - j) Pi)ᵀ by
      rw [e]; exact h.1.2.transpose
    ext a b
    have := h.1.2.isHermitian.apply a b
    simp only [Matrix.neg_apply, star_neg, neg_inj] at this
    simp only [Matrix.neg_apply, Matrix.map_apply, Matrix.transpose_apply, neg_inj]
    rw [← this]; simp
  · have := h.2 (h'.map (starRingEnd ℂ)) (fun a b hab => by simp [hb a b hab]) k
    have e1 : Pi.map (starRingEnd ℂ) * h' = (Pi * h'.map (starRingEnd ℂ)).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.mul_apply]
    have e2 : (h'ᴴ * G.map (starRingEnd ℂ) * h').submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) = (((h'.map (starRingEnd ℂ))ᴴ * G * h'.map (starRingEnd ℂ)).submatrix
          (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
          (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.mul_apply]
    rw [e1, g, e2, dm, dm, Complex.norm_conj, Complex.norm_conj, this]

theorem blockG_conj {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :
    blockG (Γ.map (starRingEnd ℂ)) = (blockG Γ).map (starRingEnd ℂ) := by
  have e : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ⁻¹ = ((omBlock Γ)ᵀ⁻¹).map (starRingEnd ℂ) := by
    have e1 : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ = (omBlock Γ)ᴴ := rfl
    rw [e1, ← Matrix.conjTranspose_nonsing_inv, ← Matrix.transpose_nonsing_inv]
    rfl
  ext a b
  simp only [blockG, e, Matrix.submatrix_apply, Matrix.map_apply]
  rcases (blockEquiv p q).symm a with a | a <;> rcases (blockEquiv p q).symm b with b | b <;>
    simp [wBlock]

end PositivityTheory.Xgp.c_bm_exists_period
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_period

open scoped MatrixOrder in
theorem exists_sqrt {m : Type} [Fintype m] [DecidableEq m] {G : Matrix m m ℂ} (h : G.PosDef) :
    ∃ R : Matrix m m ℂ, G = Rᴴ * R ∧ R.det ≠ 0 := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.posSemidef.nonneg
  refine ⟨R, by rw [hR, star_eq_conjTranspose], ?_⟩
  intro h0
  have hz : G.det = 0 := by
    rw [hR, star_eq_conjTranspose, det_mul, h0, mul_zero]
  have hu := (Matrix.isUnit_iff_isUnit_det G).mp h.isUnit
  rw [hz] at hu
  exact not_isUnit_zero hu

private theorem sub_transpose_eq_fromRows_conj_fromBlocks {p q : ℕ} (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ)
    (Bm : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (Go : Matrix (Fin q) (Fin q) ℂ) (Gw : Matrix (Fin p) (Fin p) ℂ) :
    Aᴴ * Gw * A - (Bmᴴ * Go * Bm)ᵀ =
      (fromRows (Bm.map (starRingEnd ℂ)) A)ᴴ * fromBlocks (-Goᵀ) 0 0 Gw *
        fromRows (Bm.map (starRingEnd ℂ)) A := by
  have hN : (fromRows (Bm.map (starRingEnd ℂ)) A)ᴴ = fromCols Bmᵀ Aᴴ := by
    ext i (j | j) <;> simp [conjTranspose_apply]
  have h2 : fromBlocks (-Goᵀ) 0 0 Gw * fromRows (Bm.map (starRingEnd ℂ)) A =
      fromRows (-Goᵀ * Bm.map (starRingEnd ℂ)) (Gw * A) := by
    ext (i | i) j <;> simp [mul_apply, Fintype.sum_sum_type]
  have h3 : Bmᴴᵀ = Bm.map (starRingEnd ℂ) := by
    ext i j
    simp [conjTranspose_apply]
  conv_rhs => rw [Matrix.mul_assoc, h2, hN, fromCols_mul_fromRows]
  rw [transpose_mul, transpose_mul, h3]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

private theorem fromRows_mul_neg_inv_mul_transpose {p q : ℕ} (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ)
    (Bm : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (Go : Matrix (Fin q) (Fin q) ℂ) (Gw : Matrix (Fin p) (Fin p) ℂ)
    (Ψ : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (hGo : Goᵀ.det ≠ 0)
    (hN : (fromRows (Bm.map (starRingEnd ℂ)) A).det ≠ 0) (hΨd : Ψ.det ≠ 0)
    (hΨ : Ψ = (fromRows (Bm.map (starRingEnd ℂ)) A)ᴴ * fromBlocks (-Goᵀ) 0 0 Gw *
        fromRows (Bm.map (starRingEnd ℂ)) A) :
    fromRows (Bm.map (starRingEnd ℂ)) A * (-Ψ⁻¹ * Bmᵀ) = fromRows Goᵀ⁻¹ (0 : Matrix (Fin p) (Fin q) ℂ) := by
  set Nm := fromRows (Bm.map (starRingEnd ℂ)) A with hNm
  have hNu : IsUnit Nm.det := isUnit_iff_ne_zero.mpr hN
  have hΨu : IsUnit Ψ.det := isUnit_iff_ne_zero.mpr hΨd
  have hGu : IsUnit Goᵀ.det := isUnit_iff_ne_zero.mpr hGo
  have hNh : Nmᴴ = fromCols Bmᵀ Aᴴ := by
    ext i (j | j) <;> simp [hNm, conjTranspose_apply]
  have hDF : fromBlocks (-Goᵀ) 0 0 Gw * fromRows Goᵀ⁻¹ (0 : Matrix (Fin p) (Fin q) ℂ) =
      fromRows (-1) (0 : Matrix (Fin p) (Fin q) ℂ) := by
    have : Goᵀ * Goᵀ⁻¹ = 1 := mul_nonsing_inv _ hGu
    ext (i | i) j <;> simp [mul_apply, Fintype.sum_sum_type, ← this]
  have hW : Ψ * (Nm⁻¹ * fromRows Goᵀ⁻¹ (0 : Matrix (Fin p) (Fin q) ℂ)) = -Bmᵀ := by
    rw [hΨ, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Nm Nm⁻¹,
      mul_nonsing_inv _ hNu, Matrix.one_mul, hDF, hNh, fromCols_mul_fromRows]
    simp
  have hW2 : Nm⁻¹ * fromRows Goᵀ⁻¹ (0 : Matrix (Fin p) (Fin q) ℂ) = -Ψ⁻¹ * Bmᵀ := by
    have := congrArg (fun M => Ψ⁻¹ * M) hW
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hΨu, Matrix.one_mul] at this
    rw [this, Matrix.mul_neg, Matrix.neg_mul]
  rw [← hW2, ← Matrix.mul_assoc, mul_nonsing_inv _ hNu, Matrix.one_mul]

private theorem fromBlocks_conj_inv_eq_conj {p q : ℕ} (G : Matrix (Fin q) (Fin q) ℂ) (hG : G.PosDef)
    (Y : Matrix (Fin q) (Fin p) ℂ) (Gw : Matrix (Fin p) (Fin p) ℂ) :
    (fromBlocks G⁻¹ Y 0 1)ᴴ * fromBlocks (-G) 0 0 Gw * fromBlocks G⁻¹ Y 0 1 =
      (fromBlocks 1 (G * Y) 0 1)ᴴ * fromBlocks (-G⁻¹) 0 0 Gw * fromBlocks 1 (G * Y) 0 1 := by
  have hGu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hK : (G⁻¹)ᴴ = G⁻¹ := by
    rw [conjTranspose_nonsing_inv, hG.1.eq]
  have hsplit : fromBlocks G⁻¹ Y 0 (1 : Matrix (Fin p) (Fin p) ℂ) =
      fromBlocks G⁻¹ 0 0 1 * fromBlocks 1 (G * Y) 0 1 := by
    rw [fromBlocks_multiply]
    simp [← Matrix.mul_assoc, nonsing_inv_mul _ hGu]
  have hmid : (fromBlocks G⁻¹ 0 0 (1 : Matrix (Fin p) (Fin p) ℂ))ᴴ * fromBlocks (-G) 0 0 Gw *
      fromBlocks G⁻¹ 0 0 1 = fromBlocks (-G⁻¹) 0 0 Gw := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [hK, Matrix.mul_assoc, mul_nonsing_inv _ hGu]
  rw [hsplit, conjTranspose_mul, ← hmid]
  simp only [Matrix.mul_assoc]

private theorem gramOf_sigForm_submatrix_blockEquiv {p q : ℕ} (P : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) :
    (gramOf (sigForm (p + q) p) (P.submatrix (blockEquiv p q).symm (blockEquiv p q).symm)).submatrix
      (blockEquiv p q) (blockEquiv p q) =
      Pᴴ * fromBlocks (-1 : Matrix (Fin q) (Fin q) ℂ) 0 0 (1 : Matrix (Fin p) (Fin p) ℂ) * P := by
  unfold gramOf
  rw [← submatrix_mul_equiv _ _ _ (blockEquiv p q), ← submatrix_mul_equiv _ _ _ (blockEquiv p q),
    conjTranspose_submatrix, submatrix_submatrix, submatrix_submatrix, submatrix_diagonal_equiv]
  simp only [Equiv.symm_comp_self, submatrix_id_id]
  congr 2
  ext (i | i) (j | j) <;> simp [diagonal_apply, sigForm, blockEquiv, one_apply] <;> split_ifs <;> simp

theorem exists_periodMatrix {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {p q : ℕ} {B : Set X} (hB : IsOpen B)
    {u₀ : X} (hu₀ : u₀ ∈ B) {A : X → Matrix (Fin p) (Fin q ⊕ Fin p) ℂ} {Bm : X → Matrix (Fin q) (Fin q ⊕ Fin p) ℂ}
    (hA : HolM B A) (hBm : HolM B Bm) {Go : X → Matrix (Fin q) (Fin q) ℂ} {Gw : X → Matrix (Fin p) (Fin p) ℂ}
    (hGo : ∀ u ∈ B, (Go u).PosDef) (hGw : ∀ u ∈ B, (Gw u).PosDef) {Ψ : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ}
    (hΨ : ∀ u ∈ B, Ψ = (A u)ᴴ * Gw u * A u - ((Bm u)ᴴ * Go u * Bm u)ᵀ)
    (hM : (fromRows ((Bm u₀).map (starRingEnd ℂ)) (A u₀)).det ≠ 0) :
    ∃ (B' : Set X) (Pi : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), IsOpen B' ∧ u₀ ∈ B' ∧ B' ⊆ B ∧ HolM B' Pi ∧
      (∀ u ∈ B', IsPeriodGram p (Pi u)
        ((fromBlocks (Go u)ᵀ⁻¹ 0 0 (Gw u)).submatrix (blockEquiv p q).symm (blockEquiv p q).symm)) ∧
      ∀ v : X, (∀ a b : Fin (p + q), p + q - p ≤ (a : ℕ) → (b : ℕ) < p + q - p → ((Pi u₀)⁻¹ * dM Pi u₀ v) a b = 0) →
        ∀ (α : Matrix (Fin p) (Fin p) ℂ) (β : Matrix (Fin p) (Fin q) ℂ),
          dM A u₀ v = α * A u₀ + β * (Bm u₀).map (starRingEnd ℂ) → β = 0 := by
  classical
  have hinl : ∀ i : Fin q, ((blockEquiv p q (Sum.inl i) : Fin (p + q)) : ℕ) = i := by
    intro i
    simp [blockEquiv]
  have hinr : ∀ i : Fin p, ((blockEquiv p q (Sum.inr i) : Fin (p + q)) : ℕ) = q + i := by
    intro i
    simp [blockEquiv]
    omega
  obtain ⟨R1, hR1, hR1d⟩ := exists_sqrt ((hGo u₀ hu₀).transpose)
  obtain ⟨R2, hR2, hR2d⟩ := exists_sqrt (hGw u₀ hu₀)
  have hPsi : ∀ x ∈ B, Ψ = (fromRows ((Bm x).map (starRingEnd ℂ)) (A x))ᴴ *
      fromBlocks (-(Go x)ᵀ) 0 0 (Gw x) * fromRows ((Bm x).map (starRingEnd ℂ)) (A x) :=
    fun x hx => (hΨ x hx).trans (sub_transpose_eq_fromRows_conj_fromBlocks _ _ _ _)
  have hGoTd : ∀ x ∈ B, ((Go x)ᵀ).det ≠ 0 := fun x hx =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (hGo x hx).transpose.isUnit).ne_zero
  have hGwd : ∀ x ∈ B, (Gw x).det ≠ 0 := fun x hx =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (hGw x hx).isUnit).ne_zero
  have hDd : ∀ x ∈ B, (fromBlocks (-(Go x)ᵀ) 0 0 (Gw x)).det ≠ 0 := by
    intro x hx
    rw [det_fromBlocks_zero₂₁, det_neg]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hGoTd x hx)) (hGwd x hx)
  have hΨd : Ψ.det ≠ 0 := by
    rw [hPsi u₀ hu₀, det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr hM) (hDd u₀ hu₀)) hM
  have hNd : ∀ x ∈ B, (fromRows ((Bm x).map (starRingEnd ℂ)) (A x)).det ≠ 0 := by
    intro x hx h0
    apply hΨd
    rw [hPsi x hx, det_mul, h0, mul_zero]
  let Q1f : X → Matrix (Fin q ⊕ Fin p) (Fin q) ℂ := fun x => -Ψ⁻¹ * (Bm x)ᵀ
  have hQ1 : ∀ x ∈ B, fromRows ((Bm x).map (starRingEnd ℂ)) (A x) * Q1f x =
      fromRows ((Go x)ᵀ⁻¹) (0 : Matrix (Fin p) (Fin q) ℂ) :=
    fun x hx => fromRows_mul_neg_inv_mul_transpose _ _ _ _ _ (hGoTd x hx) (hNd x hx) hΨd (hPsi x hx)
  have hAQ1 : ∀ x ∈ B, A x * Q1f x = 0 := by
    intro x hx
    have h1 := hQ1 x hx
    rw [fromRows_mul] at h1
    exact ((fromRows_ext_iff _ _ _ _).mp h1).2
  have hBQ1 : ∀ x ∈ B, (Bm x).map (starRingEnd ℂ) * Q1f x = (Go x)ᵀ⁻¹ := by
    intro x hx
    have h1 := hQ1 x hx
    rw [fromRows_mul] at h1
    exact ((fromRows_ext_iff _ _ _ _).mp h1).1
  have hQ1h : HolM B Q1f := (HolM.const B (-Ψ⁻¹)).mul (fun i j => hBm j i)
  have hMu : IsUnit (fromRows ((Bm u₀).map (starRingEnd ℂ)) (A u₀)).det := isUnit_iff_ne_zero.mpr hM
  let C : Matrix (Fin q ⊕ Fin p) (Fin p) ℂ := (fromRows ((Bm u₀).map (starRingEnd ℂ)) (A u₀))⁻¹ *
    fromRows (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin p) (Fin p) ℂ)
  have hAC : A u₀ * C = 1 := by
    have h1 : fromRows ((Bm u₀).map (starRingEnd ℂ)) (A u₀) * C =
        fromRows (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin p) (Fin p) ℂ) := by
      simp only [C]
      rw [← Matrix.mul_assoc, mul_nonsing_inv _ hMu, Matrix.one_mul]
    rw [fromRows_mul] at h1
    exact ((fromRows_ext_iff _ _ _ _).mp h1).2
  have hACh : HolM B (fun x => A x * C) := hA.mul (HolM.const B C)
  let B' : Set X := {x | x ∈ B ∧ (A x * C).det ≠ 0}
  have hB'o : IsOpen B' := HolM.isOpen_det hACh hB
  have hu₀' : u₀ ∈ B' := ⟨hu₀, by rw [hAC]; simp⟩
  have hB'B : B' ⊆ B := fun x hx => hx.1
  let Q : X → Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ := fun x => fromCols (Q1f x) (C * (A x * C)⁻¹)
  let T : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ :=
    fromBlocks R1 0 0 R2 * fromRows ((Bm u₀).map (starRingEnd ℂ)) (A u₀)
  have hTJT : Tᴴ * fromBlocks (-1 : Matrix (Fin q) (Fin q) ℂ) 0 0 (1 : Matrix (Fin p) (Fin p) ℂ) * T = Ψ := by
    have hS : (fromBlocks R1 0 0 R2)ᴴ * fromBlocks (-1 : Matrix (Fin q) (Fin q) ℂ) 0 0
        (1 : Matrix (Fin p) (Fin p) ℂ) * fromBlocks R1 0 0 R2 = fromBlocks (-(Go u₀)ᵀ) 0 0 (Gw u₀) := by
      rw [hR1, hR2]
      simp [fromBlocks_conjTranspose, fromBlocks_multiply]
    rw [hPsi u₀ hu₀, ← hS]
    simp only [T, conjTranspose_mul, Matrix.mul_assoc]
  let Pi : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ :=
    fun x => (T * Q x).submatrix (blockEquiv p q).symm (blockEquiv p q).symm
  have hQ2h : HolM B' (fun x => C * (A x * C)⁻¹) :=
    (HolM.const B' C).mul (HolM.inv (hACh.mono hB'B) (fun x hx => hx.2))
  have hQh : HolM B' Q := by
    intro a b
    rcases b with b | b
    · exact (hQ1h.mono hB'B) a b
    · exact hQ2h a b
  have hTQh : HolM B' (fun x => T * Q x) := (HolM.const B' T).mul hQh
  have hPih : HolM B' Pi := fun a b => hTQh _ _
  have hNQ : ∀ x ∈ B', fromRows ((Bm x).map (starRingEnd ℂ)) (A x) * Q x =
      fromBlocks ((Go x)ᵀ⁻¹) ((Bm x).map (starRingEnd ℂ) * (C * (A x * C)⁻¹)) 0 1 := by
    intro x hx
    have hAQ2 : A x * (C * (A x * C)⁻¹) = 1 := by
      rw [← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx.2)]
    simp only [Q]
    rw [mul_fromCols, hQ1 x hx.1, fromRows_mul, hAQ2, fromCols_fromRows_eq_fromBlocks]
  have hQd : ∀ x ∈ B', (Q x).det ≠ 0 := by
    intro x hx h0
    have h1 := congrArg det (hNQ x hx)
    rw [det_mul, h0, mul_zero, det_fromBlocks_zero₂₁, det_one, mul_one] at h1
    have hu : IsUnit ((Go x)ᵀ).det := isUnit_iff_ne_zero.mpr (hGoTd x hx.1)
    exact (isUnit_nonsing_inv_det _ hu).ne_zero h1.symm
  have hTd : T.det ≠ 0 := by
    simp only [T]
    rw [det_mul, det_fromBlocks_zero₂₁]
    exact mul_ne_zero (mul_ne_zero hR1d hR2d) hM
  refine ⟨B', Pi, hB'o, hu₀', hB'B, hPih, ?_, ?_⟩
  · intro x hx
    apply periodGram_of (Pi x) ((Go x)ᵀ⁻¹) (Gw x)
      ((Go x)ᵀ * ((Bm x).map (starRingEnd ℂ) * (C * (A x * C)⁻¹))) ((hGo x hx.1).transpose.inv)
    · apply isUnit_iff_ne_zero.mpr
      simp only [Pi]
      rw [det_submatrix_equiv_self, det_mul]
      exact mul_ne_zero hTd (hQd x hx)
    · simp only [Pi]
      rw [gramOf_sigForm_submatrix_blockEquiv]
      calc (T * Q x)ᴴ * fromBlocks (-1 : Matrix (Fin q) (Fin q) ℂ) 0 0 (1 : Matrix (Fin p) (Fin p) ℂ) *
            (T * Q x)
          = (Q x)ᴴ * (Tᴴ * fromBlocks (-1 : Matrix (Fin q) (Fin q) ℂ) 0 0 (1 : Matrix (Fin p) (Fin p) ℂ) * T) *
            Q x := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = (fromRows ((Bm x).map (starRingEnd ℂ)) (A x) * Q x)ᴴ * fromBlocks (-(Go x)ᵀ) 0 0 (Gw x) *
            (fromRows ((Bm x).map (starRingEnd ℂ)) (A x) * Q x) := by
            rw [hTJT, hPsi x hx.1]
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by
            rw [hNQ x hx]
            exact fromBlocks_conj_inv_eq_conj _ (hGo x hx.1).transpose _ _
  · intro v hv α β hd
    have hnhds : B' ∈ nhds u₀ := hB'o.mem_nhds hu₀'
    have hdTQ : dM (fun x => T * Q x) u₀ v = T * dM Q u₀ v := by
      rw [dM_mul (HolM.const B' T) hQh hnhds,
        dM_const (A := fun _ => T) (C := T) (Filter.Eventually.of_forall fun _ => rfl) v,
        Matrix.zero_mul, zero_add]
    have hdPi : dM Pi u₀ v = (T * dM Q u₀ v).submatrix (blockEquiv p q).symm (blockEquiv p q).symm := by
      rw [← hdTQ]
      rfl
    have hTu : IsUnit T.det := isUnit_iff_ne_zero.mpr hTd
    have hPi0 : (Pi u₀)⁻¹ * dM Pi u₀ v =
        ((Q u₀)⁻¹ * dM Q u₀ v).submatrix (blockEquiv p q).symm (blockEquiv p q).symm := by
      rw [hdPi]
      simp only [Pi]
      rw [inv_submatrix_equiv, submatrix_mul_equiv, Matrix.mul_inv_rev, Matrix.mul_assoc,
        ← Matrix.mul_assoc T⁻¹ T, nonsing_inv_mul _ hTu, Matrix.one_mul]
    have hz : ∀ i : Fin p, ∀ j : Fin q, ((Q u₀)⁻¹ * dM Q u₀ v) (Sum.inr i) (Sum.inl j) = 0 := by
      intro i j
      have h1 := hv (blockEquiv p q (Sum.inr i)) (blockEquiv p q (Sum.inl j))
        (by rw [hinr]; omega) (by rw [hinl]; omega)
      rw [hPi0] at h1
      simpa using h1
    have hAQ0 : A u₀ * Q u₀ = fromCols (0 : Matrix (Fin p) (Fin q) ℂ) (1 : Matrix (Fin p) (Fin p) ℂ) := by
      simp only [Q]
      rw [mul_fromCols, hAQ1 u₀ hu₀, ← Matrix.mul_assoc, hAC, inv_one, Matrix.one_mul]
    have hA0 : A u₀ = fromCols (0 : Matrix (Fin p) (Fin q) ℂ) (1 : Matrix (Fin p) (Fin p) ℂ) * (Q u₀)⁻¹ := by
      rw [← hAQ0, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hQd u₀ hu₀')), Matrix.mul_one]
    have hsel : ∀ (W : Matrix (Fin q ⊕ Fin p) (Fin q) ℂ) (i : Fin p) (j : Fin q),
        (fromCols (0 : Matrix (Fin p) (Fin q) ℂ) (1 : Matrix (Fin p) (Fin p) ℂ) * W) i j = W (Sum.inr i) j := by
      intro W i j
      simp [mul_apply, Fintype.sum_sum_type, one_apply]
    have hAdQ1 : A u₀ * dM Q1f u₀ v = 0 := by
      ext i j
      rw [hA0, Matrix.mul_assoc, hsel]
      exact hz i j
    have hAQ1d : dM (fun x => A x * Q1f x) u₀ v = 0 :=
      dM_const (C := 0) (Filter.eventually_of_mem (hB.mem_nhds hu₀) (fun x hx => hAQ1 x hx)) v
    rw [dM_mul hA hQ1h (hB.mem_nhds hu₀), hAdQ1, add_zero, hd, Matrix.add_mul, Matrix.mul_assoc,
      hAQ1 u₀ hu₀, Matrix.mul_zero, zero_add, Matrix.mul_assoc, hBQ1 u₀ hu₀] at hAQ1d
    have h2 := congrArg (· * (Go u₀)ᵀ) hAQ1d
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hGoTd u₀ hu₀)), Matrix.mul_one,
      Matrix.zero_mul] at h2
    exact h2

end PositivityTheory.Xgp.c_bm_exists_period
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.c_bm_exists_period

open GlobalTheory.PeriodChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

open Classical in

noncomputable def Pr (ty : Fin g → (E →+* ℂ)) (t : E →+* ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  diagonal fun i => if ty i = t then 1 else 0


theorem Pr_map (ty : Fin g → (E →+* ℂ)) (t : E →+* ℂ) : (Pr ty t).map (starRingEnd ℂ) = Pr ty t := by
  ext a b
  simp only [Pr, Matrix.map_apply, diagonal_apply]
  split_ifs <;> simp

theorem Pr_mul_self (ty : Fin g → (E →+* ℂ)) (t : E →+* ℂ) : Pr ty t * Pr ty t = Pr ty t := by
  simp only [Pr, diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem Pr_mul_ne (ty : Fin g → (E →+* ℂ)) {t t' : E →+* ℂ} (h : t ≠ t') : Pr ty t * Pr ty t' = 0 := by
  simp only [Pr, diagonal_mul_diagonal]
  rw [← diagonal_zero]
  congr 1
  funext i
  by_cases h1 : ty i = t
  · simp [h1, h]
  · simp [h1]

theorem exists_coord {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {ty : Fin g → (E →+* ℂ)} {t : E →+* ℂ}
    {r : ℕ} (hr : Nat.card {i // ty i = t} = r) {B : Set X} (hB : IsOpen B) {u₀ : X} (hu₀ : u₀ ∈ B)
    {W : X → Matrix (Fin g) (Fin r) ℂ} (hW : HolM B W) (hs : ∀ u ∈ B, ∀ i a, ty i ≠ t → W u i a = 0)
    (hi : ∀ c, W u₀ *ᵥ c = 0 → c = 0) :
    ∃ (B₁ : Set X) (L : X → Matrix (Fin r) (Fin g) ℂ), IsOpen B₁ ∧ u₀ ∈ B₁ ∧ B₁ ⊆ B ∧ HolM B₁ L ∧
      ∀ u ∈ B₁, L u * W u = 1 ∧ W u * L u = Pr ty t := by
  classical
  subst hr
  let e : Fin (Nat.card {i // ty i = t}) ≃ {i // ty i = t} := (Finite.equivFin _).symm
  let S : Matrix (Fin (Nat.card {i // ty i = t})) (Fin g) ℂ := Matrix.of fun a k => if k = (e a).1 then 1 else 0
  have hS : Sᵀ * S = Pr ty t := by
    ext i k
    simp only [S, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Pr, diagonal_apply]
    by_cases hit : ty i = t
    · rw [Finset.sum_eq_single (e.symm ⟨i, hit⟩)]
      · simp [hit, eq_comm]
      · intro b _ hb
        rw [if_neg, zero_mul]
        intro h
        exact hb (by rw [Equiv.eq_symm_apply]; exact Subtype.ext h.symm)
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [hit]
      · intro b _
        rw [if_neg, zero_mul]
        intro h
        exact hit (h ▸ (e b).2)
  have hP : ∀ u ∈ B, Sᵀ * (S * W u) = W u := fun u hu => by
    rw [← Matrix.mul_assoc, hS]
    ext i a
    rw [Pr, diagonal_mul]
    by_cases hit : ty i = t
    · simp [hit]
    · simp [hit, hs u hu i a hit]
  have hSW : HolM B fun u => S * W u := (HolM.const _ _).mul hW
  refine ⟨{u ∈ B | (S * W u).det ≠ 0}, fun u => (S * W u)⁻¹ * S, hSW.isOpen_det hB, ⟨hu₀, fun h0 => ?_⟩,
    fun _ h => h.1, ((hSW.mono fun _ h => h.1).inv fun _ h => h.2).mul (HolM.const _ _), fun u hu => ⟨?_, ?_⟩⟩
  · obtain ⟨c, hc, h⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine hc (hi c ?_)
    rw [← hP u₀ hu₀, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · rw [Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hu.2)
  · rw [← hS]
    conv_lhs => rw [← hP u hu.1]
    rw [hP u hu.1, ← Matrix.mul_assoc]
    congr 1
    nth_rewrite 1 [← hP u hu.1]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hu.2), Matrix.mul_one]

theorem herm_dg {ty : Fin g → (E →+* ℂ)} {G : Matrix (Fin g) (Fin g) ℂ} (hG : ∀ i k, ty i ≠ ty k → G i k = 0)
    (a : 𝓞 E) (z w : Fin g → ℂ) :
    hermForm G (dg ty a *ᵥ z) w = ∑ σ : E →+* ℂ, σ (a : E) * hermForm G (Pr ty σ *ᵥ z) (Pr ty σ *ᵥ w) := by
  classical
  simp only [hermForm, dg, Pr, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Finset.mul_sum]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.star_apply, Matrix.mulVec_diagonal]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (E →+* ℂ)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset (E →+* ℂ)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single (ty i)]
  · by_cases h : ty k = ty i
    · simp [h, diagonal_apply]; ring
    · simp [hG i k (Ne.symm h)]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem herm_block {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    {G : Matrix (Fin g) (Fin g) ℂ} (hE : ∀ x y, (hermForm G (P x) (P y)).im = D.EF x y) (i k : Fin g)
    (h : ty i ≠ ty k) : G i k = 0 :=
  (comm_iff ty ty Gᵀ).1 (herm_comm P ((lin_iff P).1 hP.1) hP.2.2.2.1 G hE) k i (Ne.symm h)

theorem form_const {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P P' : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (hP' : IsPeriod D ty P') {G G' : Matrix (Fin g) (Fin g) ℂ} (hE : ∀ x y, (hermForm G (P x) (P y)).im = D.EF x y)
    (hE' : ∀ x y, (hermForm G' (P' x) (P' y)).im = D.EF x y) (x y : D.La) (s : E →+* ℂ) :
    hermForm G (Pr ty s *ᵥ P x) (Pr ty s *ᵥ P y) - starRingEnd ℂ (hermForm G
      (Pr ty (ComplexEmbedding.conjugate s) *ᵥ P x) (Pr ty (ComplexEmbedding.conjugate s) *ᵥ P y)) =
    hermForm G' (Pr ty s *ᵥ P' x) (Pr ty s *ᵥ P' y) - starRingEnd ℂ (hermForm G'
      (Pr ty (ComplexEmbedding.conjugate s) *ᵥ P' x) (Pr ty (ComplexEmbedding.conjugate s) *ᵥ P' y)) := by
  classical
  have key : ∀ {P : D.La →+ (Fin g → ℂ)} (_ : IsPeriod D ty P) {G : Matrix (Fin g) (Fin g) ℂ}
      (_ : ∀ x y, (hermForm G (P x) (P y)).im = D.EF x y) (a : 𝓞 E),
      ∑ σ : E →+* ℂ, σ (a : E) * (hermForm G (Pr ty σ *ᵥ P x) (Pr ty σ *ᵥ P y) - starRingEnd ℂ (hermForm G
        (Pr ty (ComplexEmbedding.conjugate σ) *ᵥ P x) (Pr ty (ComplexEmbedding.conjugate σ) *ᵥ P y))) =
        ((2 * (D.EF (a • x) y : ℝ) : ℝ) : ℂ) * Complex.I := by
    intro P hP G hE a
    rw [← hE, ← Complex.sub_conj, (lin_iff P).1 hP.1, herm_dg (herm_block hP hE), map_sum]
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    refine Fintype.sum_equiv (ComplexEmbedding.involutive_conjugate E).toPerm _ _ fun σ => ?_
    simp
  let f : (E →+* ℂ) → (𝓞 E →* ℂ) := fun σ => (σ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hf : Function.Injective f := fun σ σ' h =>
    IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => DFunLike.congr_fun h a
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp f hf
  rw [← sub_eq_zero]
  refine Fintype.linearIndependent_iff.1 li (fun σ => (hermForm G (Pr ty σ *ᵥ P x) (Pr ty σ *ᵥ P y) -
      starRingEnd ℂ (hermForm G (Pr ty (ComplexEmbedding.conjugate σ) *ᵥ P x)
        (Pr ty (ComplexEmbedding.conjugate σ) *ᵥ P y))) - (hermForm G' (Pr ty σ *ᵥ P' x) (Pr ty σ *ᵥ P' y) -
      starRingEnd ℂ (hermForm G' (Pr ty (ComplexEmbedding.conjugate σ) *ᵥ P' x)
        (Pr ty (ComplexEmbedding.conjugate σ) *ᵥ P' y)))) ?_ s
  funext a
  have := sub_eq_zero.2 ((key hP hE a).trans (key hP' hE' a).symm)
  rw [← Finset.sum_sub_distrib] at this
  rw [Finset.sum_apply, Pi.zero_apply, ← this]
  refine Finset.sum_congr rfl fun σ _ => ?_
  show _ * σ (a : E) = _
  ring

theorem exists_cols {Λ I : Type} [Fintype I] [DecidableEq I] (f : Λ → I → ℂ)
    (hC : Submodule.span ℂ (Set.range f) = ⊤) : ∃ x : I → Λ, (Matrix.of fun a j => f (x j) a).det ≠ 0 := by
  classical
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ (Set.range f)
  let bb := Module.Basis.mk hli (by simp [hspan, hC])
  haveI : Fintype b := Module.Basis.fintypeIndexOfRankLtAleph0 bb (Module.rank_lt_aleph0 ℂ _)
  have hcard : Fintype.card I = Fintype.card b := by simpa using (Module.finrank_eq_card_basis bb)
  let e : I ≃ b := Fintype.equivOfCardEq hcard
  choose y hy using fun i : b => hbS i.2
  refine ⟨fun j => y (e j), ?_⟩
  have h2 : (fun j => f (y (e j))) = (Subtype.val : b → (I → ℂ)) ∘ e := by
    funext j
    simp [hy]
  have h3 : LinearIndependent ℂ fun j => f (y (e j)) := by rw [h2]; exact hli.comp _ e.injective
  have h1 : IsUnit (Matrix.of fun j => f (y (e j))) := Matrix.linearIndependent_rows_iff_isUnit.1 h3
  rw [← det_transpose]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h1).ne_zero

theorem herm_eq {I J : Type} [Fintype I] [Fintype J] (G : Matrix (Fin g) (Fin g) ℂ) (A : Matrix (Fin g) I ℂ)
    (B : Matrix (Fin g) J ℂ) (i : I) (j : J) :
    (Aᴴ * ((Real.pi : ℂ) • Gᵀ) * B) i j = Real.pi * hermForm G (fun k => B k j) (fun k => A k i) := by
  simp only [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul,
    Matrix.smul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, Pi.star_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem posDef_K {G : Matrix (Fin g) (Fin g) ℂ} (hG : G.IsHermitian)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm G z z).re) : ((Real.pi : ℂ) • Gᵀ).PosDef := by
  have : G.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hG fun x hx => ?_
    have h1 := hp (star x) (by simpa using hx)
    have h2 := hG.im_star_dotProduct_mulVec_self x
    simp only [hermForm, star_star] at h1
    exact Complex.pos_iff.2 ⟨h1, h2.symm⟩
  exact this.transpose.smul (by exact_mod_cast Real.pi_pos)

theorem exists_period_of_frames {D : Datum H} {p q n : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty)
    {B : Set (Fin n → ℂ)} (hB : IsOpen B) {u₀ : Fin n → ℂ} (hu₀ : u₀ ∈ B)
    {P : (Fin n → ℂ) → (D.La →+ (Fin g → ℂ))} (hP : IsHolPeriods D ty B P) {s : E →+* ℂ}
    (hs : s (H.rt : E) = H.rt0) {W : Fin (p + q) → (Fin n → ℂ) → Fin g → ℂ} (hW : ∀ k, DifferentiableOn ℂ (W k) B)
    (hWo : ∀ u ∈ B, ∀ a i, ty i ≠ ComplexEmbedding.conjugate s → W (omEmb p q a) u i = 0)
    (hWw : ∀ u ∈ B, ∀ a i, ty i ≠ s → W (wEmb p q a) u i = 0) {G : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    (hG : ∀ u ∈ B, (G u).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (G u) z z).re) ∧
      ∀ x y, (hermForm (G u) (P u x) (P u y)).im = D.EF x y)
    {Γ : (Fin n → ℂ) → Matrix (Fin (p + q)) (Fin (p + q)) ℂ}
    (hΓ : ∀ u ∈ B, Γ u = Matrix.of fun i j => (Real.pi : ℂ) * hermForm (G u) (W j u) (W i u)) (h0 : (Γ u₀).PosDef) :
    ∃ (B' : Set (Fin n → ℂ)) (Pi : (Fin n → ℂ) → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), IsOpen B' ∧ u₀ ∈ B' ∧
      B' ⊆ B ∧ HolM B' Pi ∧ (∀ u ∈ B', IsPeriodGram p (Pi u) (blockG (Γ u))) ∧
      ∀ v, (∀ a b : Fin (p + q), p + q - p ≤ (a : ℕ) → (b : ℕ) < p + q - p → ((Pi u₀)⁻¹ * dM Pi u₀ v) a b = 0) →
        ∀ α β : Matrix (Fin g) (Fin g) ℂ,
          (∀ x, fderiv ℂ (fun u => P u x) u₀ v = α *ᵥ P u₀ x + β *ᵥ star (P u₀ x)) →
          (∀ i k, ty i ≠ ty k → α i k = 0) → (∀ i k, ty i ≠ ComplexEmbedding.conjugate (ty k) → β i k = 0) →
          ∀ i k, ty i = s → β i k = 0 := by
  classical
  set s' := ComplexEmbedding.conjugate s with hs'
  have hs'0 : s' (H.rt : E) ≠ H.rt0 := (conj_rt H s).1 hs
  have hne : s ≠ s' := fun h => hs'0 (h ▸ hs)
  let Wo : (Fin n → ℂ) → Matrix (Fin g) (Fin q) ℂ := fun u => Matrix.of fun i a => W (omEmb p q a) u i
  let Ww : (Fin n → ℂ) → Matrix (Fin g) (Fin p) ℂ := fun u => Matrix.of fun i a => W (wEmb p q a) u i
  let K : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun u => (Real.pi : ℂ) • (G u)ᵀ
  have hK : ∀ u ∈ B, (K u).PosDef := fun u hu => posDef_K (hG u hu).1 (hG u hu).2.1
  have eo : ∀ u ∈ B, omBlock (Γ u) = (Wo u)ᴴ * K u * Wo u := fun u hu => by
    ext a b; rw [herm_eq, hΓ u hu]; rfl
  have ew : ∀ u ∈ B, wBlock (Γ u) = (Ww u)ᴴ * K u * Ww u := fun u hu => by
    ext a b; rw [herm_eq, hΓ u hu]; rfl
  have inj : ∀ {r : ℕ} (V : Matrix (Fin g) (Fin r) ℂ), (Vᴴ * K u₀ * V).PosDef → ∀ c, V *ᵥ c = 0 → c = 0 := by
    intro r V h c hc
    by_contra h1
    have := h.dotProduct_mulVec_pos h1
    rw [← Matrix.mulVec_mulVec, hc] at this
    simp at this
  obtain ⟨B₁, Lo, hB₁, h₁, s₁, hLo, eLo⟩ := exists_coord (W := Wo) ((hty s').2 hs'0) hB hu₀
    (fun i a => differentiableOn_pi.1 (hW _) i) (fun u hu i a h => hWo u hu a i h)
    (inj _ (eo u₀ hu₀ ▸ h0.submatrix (omEmb_strictMono p q).injective))
  obtain ⟨B₂, Lw, hB₂, h₂, s₂, hLw, eLw⟩ := exists_coord (W := Ww) ((hty s).1 hs) hB hu₀
    (fun i a => differentiableOn_pi.1 (hW _) i) (fun u hu i a h => hWw u hu a i h)
    (inj _ (ew u₀ hu₀ ▸ h0.submatrix (wEmb_strictMono p q).injective))
  have LoP : ∀ u ∈ B₁, Lo u * Pr ty s' = Lo u := fun u hu => by
    rw [← (eLo u hu).2, ← Matrix.mul_assoc, (eLo u hu).1, Matrix.one_mul]
  have LwP : ∀ u ∈ B₂, Lw u * Pr ty s = Lw u := fun u hu => by
    rw [← (eLw u hu).2, ← Matrix.mul_assoc, (eLw u hu).1, Matrix.one_mul]
  have PWo : Pr ty s' * Wo u₀ = Wo u₀ := by rw [← (eLo u₀ h₁).2, Matrix.mul_assoc, (eLo u₀ h₁).1, Matrix.mul_one]
  have PWw : Pr ty s * Ww u₀ = Ww u₀ := by rw [← (eLw u₀ h₂).2, Matrix.mul_assoc, (eLw u₀ h₂).1, Matrix.mul_one]
  have LwWo : Lw u₀ * Wo u₀ = 0 := by
    rw [← LwP u₀ h₂, ← PWo, Matrix.mul_assoc, ← Matrix.mul_assoc (Pr ty s), Pr_mul_ne ty hne]; simp
  have LoWw : Lo u₀ * Ww u₀ = 0 := by
    rw [← LoP u₀ h₁, ← PWw, Matrix.mul_assoc, ← Matrix.mul_assoc (Pr ty s'), Pr_mul_ne ty hne.symm]; simp
  let m : (Fin g → ℂ) → Fin q ⊕ Fin p → ℂ := fun z => Sum.elim (star (Lo u₀ *ᵥ z)) (Lw u₀ *ᵥ z)
  have hspan : Submodule.span ℂ (Set.range fun x => m (P u₀ x)) = ⊤ := by
    have hall : ∀ z, m z ∈ Submodule.span ℂ (Set.range fun x => m (P u₀ x)) := fun z => by
      have hz : z ∈ Submodule.span ℝ (Set.range (P u₀)) := (hP.1 u₀ hu₀).2.2.2.1 ▸ Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact Submodule.subset_span ⟨a, rfl⟩
      | zero => convert Submodule.zero_mem _; ext (a | a) <;> simp [m]
      | add x y _ _ hx hy =>
        convert Submodule.add_mem _ hx hy using 1; ext (a | a) <;> simp [m, Matrix.mulVec_add]
      | smul r x _ hx =>
        convert Submodule.smul_mem _ (r : ℂ) hx using 1; ext (a | a) <;> simp [m, Matrix.mulVec_smul]
    rw [eq_top_iff, ← (Pi.basisFun ℂ (Fin q ⊕ Fin p)).span_eq, Submodule.span_le]
    rintro _ ⟨a | a, rfl⟩
    · suffices e : Pi.basisFun ℂ (Fin q ⊕ Fin p) (.inl a) = m (Wo u₀ *ᵥ Pi.single a 1) by
        rw [e]; exact hall _
      ext (b | b) <;> simp [m, Matrix.mulVec_mulVec, (eLo u₀ h₁).1, LwWo, Pi.single_apply, apply_ite,
        -Matrix.mulVec_single]
    · suffices e : Pi.basisFun ℂ (Fin q ⊕ Fin p) (.inr a) = m (Ww u₀ *ᵥ Pi.single a 1) by
        rw [e]; exact hall _
      ext (b | b) <;> simp [m, Matrix.mulVec_mulVec, (eLw u₀ h₂).1, LoWw, Pi.single_apply, -Matrix.mulVec_single]
  obtain ⟨lam, hlam⟩ := exists_cols _ hspan
  let Λ : (Fin n → ℂ) → Matrix (Fin g) (Fin q ⊕ Fin p) ℂ := fun u => Matrix.of fun i j => P u (lam j) i
  have hΛ : HolM B Λ := fun i j => differentiableOn_pi.1 (hP.2 (lam j)) i
  have h12 : u₀ ∈ B₁ ∩ B₂ := ⟨h₁, h₂⟩
  have pd : ∀ {r : ℕ} (V : Matrix (Fin g) (Fin r) ℂ) (L : Matrix (Fin r) (Fin g) ℂ), L * V = 1 → ∀ u ∈ B,
      (Vᴴ * K u * V).PosDef := fun V L h u hu => (hK u hu).conjTranspose_mul_mul_same fun c c' e => by
    have := congrArg (L *ᵥ ·) e
    simpa [Matrix.mulVec_mulVec, h] using this
  have hform : ∀ u ∈ B₁ ∩ B₂, ∀ j k, ((Lw u * Λ u)ᴴ * wBlock (Γ u) * (Lw u * Λ u) -
      ((Lo u * Λ u)ᴴ * omBlock (Γ u) * (Lo u * Λ u))ᵀ) j k = Real.pi *
      (hermForm (G u) (Pr ty s *ᵥ P u (lam k)) (Pr ty s *ᵥ P u (lam j)) - starRingEnd ℂ (hermForm (G u)
        (Pr ty s' *ᵥ P u (lam k)) (Pr ty s' *ᵥ P u (lam j)))) := fun u hu j k => by
    have e1 : (Lw u * Λ u)ᴴ * wBlock (Γ u) * (Lw u * Λ u) = (Pr ty s * Λ u)ᴴ * K u * (Pr ty s * Λ u) := by
      rw [ew u (s₁ hu.1), ← (eLw u hu.2).2]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have e2 : (Lo u * Λ u)ᴴ * omBlock (Γ u) * (Lo u * Λ u) = (Pr ty s' * Λ u)ᴴ * K u * (Pr ty s' * Λ u) := by
      rw [eo u (s₁ hu.1), ← (eLo u hu.1).2]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e1, e2, Matrix.sub_apply, Matrix.transpose_apply, herm_eq, herm_eq, mul_sub,
      ← sesq_apply (G u) (Pr ty s' *ᵥ P u (lam k)), ← (isHermitian_iff _).1 (hG u (s₁ hu.1)).1]
    rfl
  obtain ⟨B', Pi, hB', hu', hsub, hPi, hgr, hder⟩ := exists_periodMatrix (hB₁.inter hB₂) h12
    (A := fun u => Lw u * Λ u) (Bm := fun u => Lo u * Λ u)
    ((hLw.mono Set.inter_subset_right).mul (hΛ.mono fun _ h => s₁ h.1))
    ((hLo.mono Set.inter_subset_left).mul (hΛ.mono fun _ h => s₁ h.1))
    (Go := fun u => omBlock (Γ u)) (Gw := fun u => wBlock (Γ u))
    (fun u hu => by rw [eo u (s₁ hu.1)]; exact pd _ _ (eLo u hu.1).1 u (s₁ hu.1))
    (fun u hu => by rw [ew u (s₁ hu.1)]; exact pd _ _ (eLw u hu.2).1 u (s₁ hu.1))
    (Ψ := (Lw u₀ * Λ u₀)ᴴ * wBlock (Γ u₀) * (Lw u₀ * Λ u₀) - ((Lo u₀ * Λ u₀)ᴴ * omBlock (Γ u₀) * (Lo u₀ * Λ u₀))ᵀ)
    (fun u hu => by
      ext j k
      rw [hform u hu, hform u₀ h12, form_const (hP.1 u₀ hu₀) (hP.1 u (s₁ hu.1)) (hG u₀ hu₀).2.2 (hG u (s₁ hu.1)).2.2])
    (by
      convert hlam using 2
      ext (a | a) j <;> rfl)
  refine ⟨B', Pi, hB', hu', fun _ h => s₁ (hsub h).1, hPi, hgr, fun v hv α β hd hα hβ => ?_⟩
  have hn : B₂ ∈ nhds u₀ := hB₂.mem_nhds h₂
  have dΛ : dM Λ u₀ v = α * Λ u₀ + β * (Λ u₀).map (starRingEnd ℂ) := by
    ext i j
    have h1 := congrFun (hd (lam j)) i
    have h2 := fderiv_pi (𝕜 := ℂ) (φ := fun i u => P u (lam j) i) (x := u₀)
      (fun i => (hΛ i j).differentiableAt (hB.mem_nhds hu₀))
    have h3 : fderiv ℂ (fun u => P u (lam j)) u₀ v i = fderiv ℂ (fun u => P u (lam j) i) u₀ v := by
      rw [show (fun u => P u (lam j)) = fun u i => P u (lam j) i from rfl, h2]; rfl
    exact h3.symm.trans h1
  have dL : dM Lw u₀ v = dM Lw u₀ v * Pr ty s := by
    have h1 := dM_mul hLw (HolM.const B₂ (Pr ty s)) hn v
    rw [dM_const (A := fun _ => Pr ty s) (.of_forall fun _ => rfl), Matrix.mul_zero, add_zero] at h1
    rw [← h1]
    ext a b
    have : (fun u => Lw u a b) =ᶠ[nhds u₀] fun u => (Lw u * Pr ty s) a b :=
      Filter.eventually_of_mem hn fun u hu => by simp only [LwP u hu]
    simp only [dM, Matrix.of_apply, this.fderiv_eq]
  have cα : Pr ty s * α = α * Pr ty s := by
    ext i k
    rw [Pr, diagonal_mul, mul_diagonal]
    by_cases h : ty i = ty k
    · rw [h, mul_comm]
    · simp [hα i k h]
  have cβ : Pr ty s * β = β * Pr ty s' := by
    ext i k
    rw [Pr, Pr, diagonal_mul, mul_diagonal]
    by_cases h : ty i = ComplexEmbedding.conjugate (ty k)
    · have : ty i = s ↔ ty k = s' := by
        rw [h, hs']
        exact ⟨fun e => by rw [← e, ComplexEmbedding.involutive_conjugate E], fun e => by
          rw [e, ComplexEmbedding.involutive_conjugate E]⟩
      simp only [this, mul_comm]
    · simp [hβ i k h]
  have PC : (Wo u₀).map (starRingEnd ℂ) * (Lo u₀).map (starRingEnd ℂ) = Pr ty s' := by
    rw [← Matrix.map_mul, (eLo u₀ h₁).2, Pr_map]
  have hz := hder v hv ((dM Lw u₀ v + Lw u₀ * α) * Ww u₀) (Lw u₀ * β * (Wo u₀).map (starRingEnd ℂ)) (by
    rw [dM_mul hLw (hΛ.mono s₂) hn, dΛ, Matrix.map_mul]
    have a1 : (dM Lw u₀ v + Lw u₀ * α) * Ww u₀ * (Lw u₀ * Λ u₀) = dM Lw u₀ v * Λ u₀ + Lw u₀ * (α * Λ u₀) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Ww u₀), (eLw u₀ h₂).2, ← Matrix.mul_assoc, Matrix.add_mul, ← dL,
        Matrix.mul_assoc (Lw u₀), ← cα, ← Matrix.mul_assoc (Lw u₀), LwP u₀ h₂, Matrix.add_mul, Matrix.mul_assoc]
    have a2 : Lw u₀ * β * (Wo u₀).map (starRingEnd ℂ) * ((Lo u₀).map (starRingEnd ℂ) * (Λ u₀).map (starRingEnd ℂ)) =
        Lw u₀ * (β * (Λ u₀).map (starRingEnd ℂ)) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((Wo u₀).map _), PC, ← Matrix.mul_assoc, Matrix.mul_assoc (Lw u₀) β,
        ← cβ, ← Matrix.mul_assoc (Lw u₀), LwP u₀ h₂, Matrix.mul_assoc]
    rw [a1, a2, Matrix.mul_add, add_assoc])
  have hz' : Pr ty s * β = 0 := by
    have : Ww u₀ * (Lw u₀ * β * (Wo u₀).map (starRingEnd ℂ)) * (Lo u₀).map (starRingEnd ℂ) = Pr ty s * β := by
      rw [Matrix.mul_assoc (Ww u₀), Matrix.mul_assoc (Lw u₀ * β), PC, Matrix.mul_assoc (Lw u₀), ← cβ,
        ← Matrix.mul_assoc, (eLw u₀ h₂).2, ← Matrix.mul_assoc, Pr_mul_self]
    rw [← this, hz]; simp
  intro i k hi
  have := congrFun (congrFun hz' i) k
  simpa [Pr, diagonal_mul, hi] using this

end PositivityTheory.Xgp.c_bm_exists_period
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_period

open GlobalTheory.PeriodChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem mat_uniq {a b : Matrix (Fin g) (Fin g) ℂ} (h : ∀ z : Fin g → ℂ, a *ᵥ z + b *ᵥ star z = 0) : a = 0 ∧ b = 0 := by
  have key : ∀ i k, a i k = 0 ∧ b i k = 0 := fun i k => by
    have h1 := congrFun (h (Pi.single k 1)) i
    have h2 := congrFun (h (Complex.I • Pi.single k 1)) i
    simp only [star_smul, star_single, Matrix.mulVec_smul] at h1 h2
    simp at h1 h2
    constructor
    · linear_combination (1 / 2 : ℂ) * h1 - (Complex.I / 2) * h2 + (a i k - b i k) / 2 * Complex.I_mul_I
    · linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 - (a i k - b i k) / 2 * Complex.I_mul_I
  exact ⟨Matrix.ext fun i k => (key i k).1, Matrix.ext fun i k => (key i k).2⟩

theorem mat_ext {Λ : Type} {P : Λ → Fin g → ℂ} (hs : Submodule.span ℝ (Set.range P) = ⊤)
    {a b a' b' : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, a *ᵥ P x + b *ᵥ star (P x) = a' *ᵥ P x + b' *ᵥ star (P x)) :
    a = a' ∧ b = b' := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := b)]
  refine mat_uniq fun z => ?_
  have hz : z ∈ Submodule.span ℝ (Set.range P) := hs ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨x, rfl⟩ := hx; simp only [Matrix.sub_mulVec]; linear_combination h x
  | zero => simp
  | add x y _ _ hx hy => simp only [star_add, Matrix.mulVec_add]; linear_combination hx + hy
  | smul r x _ hx => rw [star_smul, star_trivial, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add, hx, smul_zero]

theorem dM_congr {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {I J : Type} {A B : X → Matrix I J ℂ} {u : X}
    (h : ∀ᶠ x in nhds u, A x = B x) (v : X) : dM A u v = dM B u v := by
  ext a b
  have : (fun x => A x a b) =ᶠ[nhds u] fun x => B x a b := h.mono fun x hx => by simp only [hx]
  simp only [dM, Matrix.of_apply, this.fderiv_eq]

theorem deriv_zero {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B) (h0 : 0 ∈ B)
    {P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))} (hP : IsHolPeriods (FU.Di i) ty B P) (v : Fin n → ℂ) :
    ∃ α β : Matrix (Fin g) (Fin g) ℂ,
      (∀ x, fderiv ℂ (fun u => P u x) 0 v = α *ᵥ P 0 x + β *ᵥ star (P 0 x)) ∧
      (∀ i k, ty i ≠ ty k → α i k = 0) ∧ (∀ i k, ty i ≠ ComplexEmbedding.conjugate (ty k) → β i k = 0) ∧
      ((∀ i k, ty i (H.rt : E) = H.rt0 → β i k = 0) → ∀ (U : Xo.X.Opens) (f : Γ(Xo.X, U)),
        ⊤ ≤ FU.u i (P 0) ⁻¹ᵁ U → fderiv ℂ (fun u => valAt' (FU.u i (P u)) U f) 0 v = 0) := by
  classical
  have hn : B ∈ nhds (0 : Fin n → ℂ) := hB.mem_nhds h0
  obtain ⟨hl, hi, hd, hs, G, hG, hp, hE⟩ := hP.1 0 h0
  have hblock := herm_block (hP.1 0 h0) hE
  rw [lin_iff] at hl
  simp only [← sesq_apply] at hp hE
  have hex : ∀ u, ∃ (Z : Matrix (Fin g) (Fin g) ℂ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), u ∈ B →
      (∀ a z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z) ∧ (∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z) ∧
      (∀ z, z ≠ 0 → (sesq G (anti Z z) (anti Z z)).re < (sesq G z z).re) ∧
      ∀ x, P u x = h (P 0 x + anti Z (P 0 x)) := fun u => by
    by_cases hu : u ∈ B
    · obtain ⟨Z, h, hh⟩ := exists_contraction (P 0) hl hi hd hs G hp hE (P u) (hP.1 u hu)
      exact ⟨Z, h, fun _ => hh⟩
    · exact ⟨0, LinearEquiv.refl _ _, fun h => absurd h hu⟩
  choose Z h hZ using hex
  let a : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun u => LinearMap.toMatrix' (h u).toLinearMap
  have ha : ∀ u z, a u *ᵥ z = h u z := fun u z => LinearMap.toMatrix'_mulVec _ _
  have had : ∀ u, (a u).det ≠ 0 := fun u e => by
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 e
    exact hy0 ((h u).injective (by rw [← ha, hy, map_zero]))
  let b : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun u => a u * Z u
  have hab : ∀ u ∈ B, ∀ x, P u x = a u *ᵥ P 0 x + b u *ᵥ star (P 0 x) := fun u hu x => by
    rw [(hZ u hu).2.2.2, ← ha, Matrix.mulVec_add, anti_apply, Matrix.mulVec_mulVec]
  have hT : ∀ z, DifferentiableOn ℂ (fun u => a u *ᵥ z + b u *ᵥ star z) B := fun z => by
    have hz : z ∈ Submodule.span ℝ (Set.range (P 0)) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => obtain ⟨x, rfl⟩ := hx; exact (hP.2 x).congr fun u hu => (hab u hu x).symm
    | zero => simpa using differentiableOn_const _
    | add x y _ _ hx hy =>
      exact (hx.add hy).congr fun u _ => by simp only [star_add, Matrix.mulVec_add, Pi.add_apply]; abel
    | smul r x _ hx =>
      exact (hx.const_smul (r : ℂ)).congr fun u _ => by
        simp only [star_smul, star_trivial, Matrix.mulVec_smul, Pi.smul_apply, smul_add, Complex.coe_smul]
  have hab' : ∀ j k, DifferentiableOn ℂ (fun u => a u j k) B ∧ DifferentiableOn ℂ (fun u => b u j k) B := by
    intro j k
    have h1 := differentiableOn_pi.1 (hT (Pi.single k 1)) j
    have h2 := differentiableOn_pi.1 (hT (Complex.I • Pi.single k 1)) j
    simp only [star_smul, star_single, Matrix.mulVec_smul] at h1 h2
    constructor
    · refine ((h1.const_mul (1 / 2)).sub (h2.const_mul (Complex.I / 2))).congr fun u _ => ?_
      simp
      linear_combination (a u j k - b u j k) / 2 * Complex.I_mul_I
    · refine ((h1.const_mul (1 / 2)).add (h2.const_mul (Complex.I / 2))).congr fun u _ => ?_
      simp
      linear_combination -(a u j k - b u j k) / 2 * Complex.I_mul_I
  have hA : HolM B a := fun j k => (hab' j k).1
  have hb : HolM B b := fun j k => (hab' j k).2
  obtain ⟨a0, b0⟩ : a 0 = 1 ∧ b 0 = 0 := mat_ext hs fun x => by rw [← hab 0 h0]; simp
  have hty : ∀ u ∈ B, (∀ j k, ¬ ty j = ty k → a u j k = 0) ∧
      ∀ j k, ¬ ty j = ComplexEmbedding.conjugate (ty k) → b u j k = 0 := fun u hu => by
    have := fun t => mat_ext hs (a := dg ty t * a u) (b := dg ty t * b u) (a' := a u * dg ty t)
      (b' := b u * dg (fun i => ComplexEmbedding.conjugate (ty i)) t) fun x => by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hab u hu,
          ← (lin_iff _).1 (hP.1 u hu).1, hab u hu, hl, star_mulVec', dg_map, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec]
    exact ⟨(comm_iff ty ty _).1 fun t => (this t).1, (comm_iff ty _ _).1 fun t => (this t).2⟩
  have dz : ∀ {c : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} {j k}, (∀ u ∈ B, c u j k = 0) → dM c 0 v j k = 0 := by
    intro c j k hc
    have : (fun u => c u j k) =ᶠ[nhds 0] fun _ => 0 := Filter.eventually_of_mem hn hc
    simp [dM, this.fderiv_eq]
  refine ⟨dM a 0 v, dM b 0 v, fun x => ?_, fun j k h => dz fun u hu => (hty u hu).1 j k h,
    fun j k h => dz fun u hu => (hty u hu).2 j k h, fun hβ U f hU => ?_⟩
  · funext j
    have h1 : (fun u => P u x j) =ᶠ[nhds 0] fun u => (a u * replicateCol Unit (P 0 x)) j () +
        (b u * replicateCol Unit (star (P 0 x))) j () :=
      Filter.eventually_of_mem hn fun u hu => congrFun (hab u hu x) j
    have h2 := congrFun (congrFun (dM_mul hA (HolM.const B (replicateCol Unit (P 0 x))) hn v) j) ()
    have h3 := congrFun (congrFun (dM_mul hb (HolM.const B (replicateCol Unit (star (P 0 x)))) hn v) j) ()
    rw [dM_const (A := fun _ => replicateCol Unit _) (.of_forall fun _ => rfl), Matrix.mul_zero, add_zero] at h2 h3
    have h4 := fderiv_pi (𝕜 := ℂ) (φ := fun j u => P u x j) (x := 0)
      (fun j => (differentiableOn_pi.1 (hP.2 x) j).differentiableAt hn)
    have h5 : fderiv ℂ (fun u => P u x) 0 v j = fderiv ℂ (fun u => P u x j) 0 v := by
      rw [show (fun u => P u x) = fun u j => P u x j from rfl, h4]; rfl
    rw [h5, h1.fderiv_eq, fderiv_fun_add (((hA.mul (HolM.const B _)) j ()).differentiableAt hn)
      (((hb.mul (HolM.const B _)) j ()).differentiableAt hn)]
    exact congrArg₂ (· + ·) h2 h3
  have hZe : ∀ u, Z u = (a u)⁻¹ * b u := fun u =>
    (Matrix.nonsing_inv_mul_cancel_left _ _ (IsUnit.mk0 _ (had u))).symm
  have hZh : HolM B Z := by
    have := (hA.inv fun u _ => had u).mul hb
    simpa only [← hZe] using this
  have Z0 : Z 0 = 0 := by rw [hZe, b0, Matrix.mul_zero]
  have dZ : dM Z 0 v = dM b 0 v := by
    have := dM_mul hA hZh hn v
    rw [Z0, a0, Matrix.mul_zero, zero_add, Matrix.one_mul] at this
    exact this.symm
  have hu : IsUnit Gᵀ.det := by
    rw [det_transpose]
    refine isUnit_det_of_ker G fun z hz h => ?_
    have := hp (star z) (by simpa using hz)
    simp [sesq_apply, hermForm, h] at this
  have dS : dM (fun u => Gᵀ * Z u) 0 v = Gᵀ * dM b 0 v := by
    rw [dM_mul (HolM.const B Gᵀ) hZh hn, dM_const (A := fun _ => Gᵀ) (.of_forall fun _ => rfl), dZ]
    simp
  have hsym : (Gᵀ * dM b 0 v)ᵀ = Gᵀ * dM b 0 v := by
    rw [← dS]
    exact dM_congr (A := fun u => (Gᵀ * Z u)ᵀ)
      (Filter.eventually_of_mem hn fun u hu => (anti_symm_iff _ _).1 (hZ u hu).2.1) v
  have hS1 : ∀ j k, ty j (H.rt : E) = H.rt0 ∨ ¬ ty k (H.rt : E) = H.rt0 → (Gᵀ * dM b 0 v) j k = 0 := by
    intro j k hjk
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : ty m (H.rt : E) = H.rt0
    · rw [hβ m k hm, mul_zero]
    rcases hjk with hj | hk
    · rw [Matrix.transpose_apply, hblock m j (fun e => hm (e ▸ hj)), zero_mul]
    · rw [dz fun u hu => (hty u hu).2 m k fun e => hm ?_, mul_zero]
      rw [e]
      by_contra hc
      exact hk ((conj_rt H (ty k)).2 hc)
  have dZ0 : dM Z 0 v = 0 := by
    have : Gᵀ * dM b 0 v = 0 := by
      ext j k
      by_cases hk : ty k (H.rt : E) = H.rt0
      · rw [← hsym, Matrix.transpose_apply]; exact hS1 k j (.inl hk)
      · exact hS1 j k (.inr hk)
    rw [dZ, ← Matrix.nonsing_inv_mul_cancel_left _ (dM b 0 v) hu, this, Matrix.mul_zero]
  let 𝒵 : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ) :=
    { carrier := {X | (∀ a, dg ty a * X = X * dg (fun i => ComplexEmbedding.conjugate (ty i)) a) ∧
        (Gᵀ * X)ᵀ = Gᵀ * X}
      add_mem' := fun {X Y} hX hY => ⟨fun a => by rw [Matrix.mul_add, Matrix.add_mul, hX.1, hY.1],
        by rw [Matrix.mul_add, Matrix.transpose_add, hX.2, hY.2]⟩
      zero_mem' := ⟨fun a => by simp, by simp⟩
      smul_mem' := fun c X hX => ⟨fun a => by rw [Matrix.mul_smul, Matrix.smul_mul, hX.1],
        by rw [Matrix.mul_smul, Matrix.transpose_smul, hX.2]⟩ }
  let e := (Module.finBasis ℂ 𝒵).equivFun
  obtain ⟨π, hπ⟩ := 𝒵.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let L : (Fin (Module.finrank ℂ 𝒵) → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ := 𝒵.subtype ∘ₗ e.symm.toLinearMap
  let R : (Fin g → Fin g → ℂ) →L[ℂ] (Fin (Module.finrank ℂ 𝒵) → ℂ) :=
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ π ∘ₗ (Matrix.ofLinearEquiv ℂ).toLinearMap)
  have hLR : ∀ u ∈ B, L (R fun j k => Z u j k) = Z u := fun u hu => by
    have hm : Z u ∈ 𝒵 := ⟨fun a => (anti_comm_iff ty a _).1 ((hZ u hu).1 a), (anti_symm_iff _ _).1 (hZ u hu).2.1⟩
    have h1 : π (Z u) = ⟨Z u, hm⟩ := DFunLike.congr_fun hπ ⟨Z u, hm⟩
    show ((e.symm (e (π (Z u))) : 𝒵) : Matrix (Fin g) (Fin g) ℂ) = Z u
    rw [e.symm_apply_apply, h1]
  obtain ⟨ho, -⟩ := isOpen_convex G hp L
  let Q : (Fin (Module.finrank ℂ 𝒵) → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ)) := fun b =>
    P 0 + (anti (L b)).toAddMonoidHom.comp (P 0)
  have hQ : IsHolPeriods (FU.Di i) ty _ Q := ⟨fun b hb => isPeriod_add (P 0) hl hi hd hs G hG hE _
    (fun a => (anti_comm_iff ty a _).2 ((e.symm b).2.1 a)) ((anti_symm_iff _ _).2 (e.symm b).2.2) hb, fun x => by
      let f : (Fin (Module.finrank ℂ 𝒵) → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
        { toFun := fun b => L b *ᵥ star (P 0 x)
          map_add' := fun b c => by rw [map_add, add_mulVec]
          map_smul' := fun c b => by rw [map_smul, smul_mulVec]; rfl }
      exact ((differentiable_const (P 0 x)).add f.toContinuousLinearMap.differentiable).differentiableOn⟩
  let w : (Fin n → ℂ) → Fin (Module.finrank ℂ 𝒵) → ℂ := fun u => R fun j k => Z u j k
  have hwm : ∀ u ∈ B, w u ∈ {b | ∀ z, z ≠ 0 → (sesq G (anti (L b) z) (anti (L b) z)).re < (sesq G z z).re} :=
    fun u hu => by
      show ∀ z, z ≠ 0 → (sesq G (anti (L (w u)) z) (anti (L (w u)) z)).re < _
      rw [hLR u hu]; exact (hZ u hu).2.2.1
  have hQP : ∀ u ∈ B, FU.u i (Q (w u)) = FU.u i (P u) := fun u hu =>
    (FU.fibre i _ _ (hQ.1 _ (hwm u hu)) (hP.1 u hu)).2 ⟨LinearEquiv.refl _ _, h u, fun _ _ => rfl,
      fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, fun x => by
        rw [LinearEquiv.refl_apply, (hZ u hu).2.2.2, ← hLR u hu]; rfl⟩
  have hF := GlobalTheory.LocalLift.hol_differentiableAt (FU.hol i _ _ Q ho hQ).1 (hwm 0 h0) (U := U)
    (by rw [hQP 0 h0]; exact hU) f
  have hZd : HasFDerivAt (fun u j k => Z u j k)
      (ContinuousLinearMap.pi fun j => ContinuousLinearMap.pi fun k => fderiv ℂ (fun u => Z u j k) 0) 0 :=
    hasFDerivAt_pi.2 fun j => hasFDerivAt_pi.2 fun k => ((hZh j k).differentiableAt hn).hasFDerivAt
  have hc := hF.hasFDerivAt.comp (0 : Fin n → ℂ) (R.hasFDerivAt.comp (0 : Fin n → ℂ) hZd)
  have he : (fun u => valAt' (FU.u i (P u)) U f) =ᶠ[nhds 0]
      (fun z => valAt' (FU.u i (Q z)) U f) ∘ w :=
    Filter.eventually_of_mem hn fun u hu => by simp only [Function.comp_apply, hQP u hu]
  rw [he.fderiv_eq, hc.fderiv]
  have : (ContinuousLinearMap.pi fun j => ContinuousLinearMap.pi fun k => fderiv ℂ (fun u => Z u j k) 0) v = 0 := dZ0
  simp only [ContinuousLinearMap.comp_apply, this, map_zero]

end PositivityTheory.Xgp.c_bm_exists_period
end

section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.c_bm_exists_period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem emb_ext {σ σ' : E →+* ℂ} (h : ∀ t : 𝓞 E, σ t = σ' t) : σ = σ' :=
  IsFractionRing.ringHom_ext (A := 𝓞 E) h

variable {Xo : ∀ l : Level H, Moduli D l} {l : Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)}
  {S : Finset ℕ} {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

theorem family_period (hN : N1c) (tie : FlagTie M 𝔐) (hpq : 1 ≤ D.p + D.q)
    {F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F) {n : ℕ}
    (p : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (τ₀ : c.F →+* ℂ)
    (hτ : (τ₀.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0)
    (hp : IsHolTo (Metric.ball 0 1) p)
    (hc : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ 𝔐.f ≫ Y.s = spMap (τ₀.comp (algebraMap (𝓞 c.F) c.F)))
    (hi : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.Interior (p u))
    (hg : M.GoodAt F (ptIdeal 𝔐.ξ M.x ⟨centre (p 0), 𝔐.all _⟩)) :
    ∃ (ρ : ℝ) (B' : Set (Fin n → ℂ)) (Pi Γ : CMType H → (Fin n → ℂ) → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
      0 < ρ ∧ ρ ≤ 1 ∧ IsOpen B' ∧ 0 ∈ B' ∧ B' ⊆ Metric.ball 0 1 ∧ (∀ τ, HolM B' (Pi τ)) ∧
      (∀ τ, ∀ u ∈ B', 𝔐.M.GramAt 𝔐.t.PP.L (p ((ρ : ℂ) • u)) (gb tie F τ) (Γ τ u) ∧
        IsPeriodGram D.p (Pi τ u) (blockG (Γ τ u))) ∧
      ∀ v, (∀ τ (a b : Fin (D.p + D.q)), D.p + D.q - D.p ≤ (a : ℕ) → (b : ℕ) < D.p + D.q - D.p →
          ((Pi τ 0)⁻¹ * dM (Pi τ) 0 v) a b = 0) →
        ∃ V : Sp (DualNumber ℂ) ⟶ 𝔐.X, IsDerivAt0 (fun u => p ((ρ : ℂ) • u)) v V ∧
          V ≫ 𝔐.f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0 ≫ 𝔐.f := by
  classical
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := hN E H D l (Xo l) _ g ty hpq hτ hty
  have hfr := fun τ => PositivityTheory.Xgp.isFrameAt_comap_gbS E H D Xo l c Y S K ι Φ y M 𝔐 tie F hF τ _ hg
  obtain ⟨i, ρ, B, P, W, G, hρ, hρ', hB, h0, hsub, hP, hW, hall, hder⟩ := model_periods 𝔐
    (fun a : CMType H × Fin (D.p + D.q) => gb tie F a.1 a.2) p τ₀ FU hp hc hi
    (fun a => GlobalTheory.T.hodge_generated_sum_specialization E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 _ _ _ (gbS tie F a.1) (p 0) (𝔐.all _) (hfr a.1) a.2)
  let s : CMType H → (E →+* ℂ) := fun τ => τ₀.comp (τ.1.codRestrict c.F (c.conj τ.1))
  have hs : ∀ τ, s τ (H.rt : E) = H.rt0 := fun τ => by
    rw [← hτ]
    exact congrArg τ₀ (Subtype.ext τ.2)
  let Γ : CMType H → (Fin n → ℂ) → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ := fun τ u =>
    Matrix.of fun i j => (Real.pi : ℂ) * hermForm (G u) (W (τ, j) u) (W (τ, i) u)
  have hΓ : ∀ τ, ∀ u ∈ B, 𝔐.M.GramAt 𝔐.t.PP.L (p ((ρ : ℂ) • u)) (gb tie F τ) (Γ τ u) := fun τ u hu =>
    (hall u hu).2.1 _ fun k => (τ, k)
  have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hpos : ∀ τ, (Γ τ 0).PosDef := fun τ => by
    have hpol := GlobalTheory.T.interior_point_polarised E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 _ (hi 0 hb0)
    obtain ⟨Γ', h1, h2⟩ := GlobalTheory.T.pair_sum_frame_at_point E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 (.inl τ) (.inr τ) (D.p + D.q)
      (gbS tie F τ) _ (𝔐.all _) hpol (hfr τ)
    have h3 := hΓ τ 0 h0
    rw [smul_zero] at h3
    rw [GlobalTheory.T.gram_matrix_change_frame E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 _ _ _ _ _ hpol h3 h1]
    exact h2
  have key := fun τ => exists_period_of_frames hty hB h0 hP (hs τ) (W := fun k => W (τ, k)) (fun k => hW _)
    (fun u hu a j hj => by
      by_contra hne
      refine hj (emb_ext fun t => ?_)
      have hm : gb tie F τ (omEmb D.p D.q a) ∈ 𝔐.Vgen (.inr τ) := by
        simp only [gb, gbS, ← blockEquiv_inl, Equiv.symm_apply_apply, Sum.elim_inl]
        exact (dualFam tie F τ a).2
      rw [mul_right_cancel₀ hne ((hall u hu).2.2 (τ, omEmb D.p D.q a) _ hm t j)]
      show s τ ((H.bar t : 𝓞 E) : E) = _
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl)
    (fun u hu a j hj => by
      by_contra hne
      refine hj (emb_ext fun t => ?_)
      have hm : gb tie F τ (wEmb D.p D.q a) ∈ 𝔐.Vgen (.inl τ) := by
        simp only [gb, gbS, ← blockEquiv_inr, Equiv.symm_apply_apply, Sum.elim_inr]
        exact wFrame_mem tie F τ a
      exact mul_right_cancel₀ hne ((hall u hu).2.2 (τ, wEmb D.p D.q a) _ hm t j))
    (fun u hu => (hall u hu).1) (Γ := Γ τ) (fun u _ => rfl) (hpos τ)
  choose B' Pi hB' h0' hsub' hPi hgr hd using key
  refine ⟨ρ, B ∩ ⋂ τ, B' τ, Pi, Γ, hρ, hρ', hB.inter (isOpen_iInter_of_finite hB'), ⟨h0, Set.mem_iInter.2 h0'⟩,
    fun u hu => hsub hu.1, fun τ => (hPi τ).mono fun u hu => Set.mem_iInter.1 hu.2 τ,
    fun τ u hu => ⟨hΓ τ u hu.1, hgr τ u (Set.mem_iInter.1 hu.2 τ)⟩, fun v hv => hder v ?_⟩
  obtain ⟨α, β, h1, h2, h3, h4⟩ := deriv_zero FU i hB h0 hP v
  refine fun U f hU => h4 (fun j k hj => ?_) U f hU
  have hinj : Function.Injective fun τ : CMType H => (⟨s τ, hs τ⟩ : CMType H) := fun τ τ' e =>
    Subtype.ext (RingHom.ext fun a => congrArg Subtype.val
      (τ₀.injective (DFunLike.congr_fun (congrArg Subtype.val e) a)))
  obtain ⟨τ, hτ'⟩ := Finite.surjective_of_injective hinj ⟨ty j, hj⟩
  exact hd τ v (hv τ) α β h1 h2 h3 j k (congrArg Subtype.val hτ').symm

theorem gramFn_eq {r : ℕ} {b : Fin r → 𝔐.Li} {z : Sp ℂ ⟶ 𝔐.X} {w : (Σ k, baseIdx ι M.blk k) → ℂ}
    {Γ : Matrix (Fin r) (Fin r) ℂ} (hw : CoordsAt 𝔐.ξ M.x z w) (hi : 𝔐.Interior z)
    (h1 : 𝔐.M.GramAt 𝔐.t.PP.L z b Γ) : HodgeMetric.gramFn 𝔐 b w = Γ := by
  have tp := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  have hex : ∃ (Γ : Matrix (Fin r) (Fin r) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
      CoordsAt 𝔐.ξ M.x z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z b Γ := ⟨Γ, z, hw, hi, h1⟩
  unfold HodgeMetric.gramFn
  rw [dif_pos hex]
  obtain ⟨z₀, hw₀, -, hΓ₀⟩ := hex.choose_spec
  have hz : z₀ = z := (tp.1 w hw.1 (tp.2.2 z w (𝔐.all _) hw).1).unique ⟨𝔐.all _, hw₀⟩ ⟨𝔐.all _, hw⟩
  rw [hz] at hΓ₀
  exact GlobalTheory.T.gram_matrix_change_frame E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z _ _ _ _
    (GlobalTheory.T.interior_point_polarised E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z hi) hΓ₀ h1

theorem exists_family {n : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) {Z : Set Rb.X} (hZ : IsClosed Z) {x : Rb.X}
    (hx : x ∉ Z) : ∃ (j : Fin Rb.A.n) (r : ℝ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)), 0 < r ∧ x ∈ (Rb.A.chart j).source ∧
      DifferentiableOn ℂ (fun u => Rb.lift x ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u))) (Metric.ball 0 1) ∧
      ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, (Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u) ∉ Z ∧
        CoordsAt 𝔐.ξ M.x (p u) (Rb.lift x ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u))) ∧
        CoordsAt 𝔐.ξ M.x (p u) (Rb.lift ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u))
          ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u))) := by
  obtain ⟨j, hj⟩ := Rb.A.cover x
  have ho : IsOpen ((Rb.A.chart j).target ∩ (Rb.A.chart j).symm ⁻¹' (Rb.U x ∩ Zᶜ)) :=
    (Rb.A.chart j).isOpen_inter_preimage_symm ((Rb.isOpen_U x).inter hZ.isOpen_compl)
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 ho (Rb.A.chart j x) ⟨(Rb.A.chart j).map_source hj, by
    rw [Set.mem_preimage, (Rb.A.chart j).left_inv hj]; exact ⟨Rb.mem_U x, hx⟩⟩
  have hm : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, Rb.A.chart j x + (r : ℂ) • u ∈
      (Rb.A.chart j).target ∩ (Rb.A.chart j).symm ⁻¹' (Rb.U x ∩ Zᶜ) := fun u hu => hb (by
    rw [mem_ball_zero_iff] at hu
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    nlinarith)
  have hex : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, ∃ z : Sp ℂ ⟶ 𝔐.X, genPt 𝔐.ξ ⤳ centre z ∧
      CoordsAt 𝔐.ξ M.x z (Rb.lift x ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u))) := fun u hu =>
    (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie _).1 (Rb.mem x _ (hm u hu).2.1)
  haveI : Nonempty (Sp ℂ ⟶ 𝔐.X) := ⟨(hex 0 (by simp)).choose⟩
  choose! p hp₀ hp using hex
  refine ⟨j, r, p, hr, hj, differentiableOn_pi.2 fun q u hu => ?_, fun u hu => ⟨(hm u hu).2.2, hp u hu, ?_⟩⟩
  · have h1 := (Rb.holo x q j _ ⟨(hm u hu).1, (hm u hu).2.1⟩).differentiableAt
    have h2 : DifferentiableAt ℂ (fun u : Fin n → ℂ => Rb.A.chart j x + (r : ℂ) • u) u := by fun_prop
    exact (h1.comp u h2).differentiableWithinAt
  · obtain ⟨a, ha, e⟩ := Rb.compat _ x _ ⟨Rb.mem_U _, (hm u hu).2.1⟩
    exact (((GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ).2.2 _ _ (𝔐.all _) (hp u hu)).2 _).2
      ⟨fun k => Units.mk0 (a k) (ha k), e⟩

theorem to_manifold {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas n X) (j : Fin A.n) {x : X}
    (hx : x ∈ (A.chart j).source) {r : ℂ} {B : Set (Fin n → ℂ)} (hB : IsOpen B) (h0 : 0 ∈ B) :
    IsOpen ((A.chart j).source ∩ (fun x' => r⁻¹ • (A.chart j x' - A.chart j x)) ⁻¹' B) ∧
    x ∈ ((A.chart j).source ∩ (fun x' => r⁻¹ • (A.chart j x' - A.chart j x)) ⁻¹' B) ∧
    ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f B →
      A.HoloOn ((A.chart j).source ∩ (fun x' => r⁻¹ • (A.chart j x' - A.chart j x)) ⁻¹' B)
        fun x' => f (r⁻¹ • (A.chart j x' - A.chart j x)) := by
  have hcont : ContinuousOn (fun x' => r⁻¹ • (A.chart j x' - A.chart j x)) (A.chart j).source :=
    ((A.chart j).continuousOn.sub continuousOn_const).const_smul r⁻¹
  refine ⟨hcont.isOpen_inter_preimage (A.chart j).open_source hB, ⟨hx, by simpa using h0⟩, fun f hf k t ht => ?_⟩
  have h1 : AnalyticAt ℂ (fun t => r⁻¹ • (A.chart j ((A.chart k).symm t) - A.chart j x)) t := by
    have := ((A.holo k j t ⟨ht.1, ht.2.1⟩).sub (analyticAt_const (v := A.chart j x))).const_smul (c := r⁻¹)
    exact this
  exact (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hB hf _ ht.2.2).comp_of_eq' h1 rfl

end PositivityTheory.Xgp.c_bm_exists_period
end
