import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Plug.Test

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CompanionTheory.Ar.Rec

attribute [-instance] GlobalTheory.CompHt.fintypePsi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

theorem degOf_eq (u : GlobalTheory.AllWt.Weight Dw) : degOf RM u = ∑ r : RootIx Dw, (-u r.1 r.2) • RM.xdeg r := by
  simp [degOf, Top.combLine, Fintype.sum_option, nOf, Top.RootModel.line, RM.x_deg]


theorem gauge_ne_zero (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw) : gauge Rd u ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (Or.lines r).1)

theorem deg_pos (Or : RootOrigin Y S RM Fx) : 0 < Or.Fl.deg := by
  have := RM.δ_pos
  rw [Or.δ_eq] at this
  exact Nat.pos_of_mul_pos_left this

theorem secZ_eq (u : GlobalTheory.AllWt.Weight Dw) :
    GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0) = Rec.secZ Xo c (GlobalTheory.AllWt.wtOf Dw u 0).1 := by
  have e : GlobalTheory.AllWt.exOf Dw u 0 = Rec.exZ Dw (GlobalTheory.AllWt.wtOf Dw u 0).1 := by
    funext i; cases i <;> simp [GlobalTheory.AllWt.exOf, Rec.exZ, Formalism.L2.Pj.exZ, GlobalTheory.AllWt.wtOf]
  ext f
  rw [GlobalTheory.AllWt.mem_secZ, e]
  simp only [Units.coe_prod]
  rfl

theorem gauge_mul (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw) {f : Rul Xo c}
    (hf : f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0)) :
    gauge Rd u * Rd.φ (evC h Z f) = Fr.rd f * ∏ r, Or.e r ^ (-nOf u (some r)) := by
  rw [secZ_eq] at hf
  rw [Rd.rd_eq _ f hf, gauge]; ring



theorem modelSmall_mono (u : GlobalTheory.AllWt.Weight Dw) : Monotone (modelSmall Or u) := by
  rintro R R' hR s ⟨h1, w, hw, h2⟩
  refine ⟨h1, w, hw, fun z hz hz' v hv => (h2 z hz hz' v hv).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hR (Finset.prod_pos fun r _ => zpow_pos ((Or.sing r).pos z hz.1) _).le




section Cone

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem cone_form (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = (∏ k, X k ^ d k) * C (aeval y g) := by
  have e := aeval_blockScale hg (fun k => (X k : MvPolynomial K Ω)) (fun p => C (y p))
  have e2 : aeval (fun p => (C (y p) : MvPolynomial K Ω)) g = C (aeval y g) := by
    have := DFunLike.congr_fun (comp_aeval y (C : Ω →+* MvPolynomial K Ω).toIntAlgHom) g
    exact this.symm
  refine Eq.trans ?_ (e.trans (congrArg _ e2))
  rw [mConeMap]
  simp only [mul_comm]
  rfl

theorem aeval_of_mem (y : (Σ k, ι k) → Ω) {g : MRing ι} (hg : g ∈ mCoordIdeal y) : aeval y g = 0 := by
  have h0 : mConeMap y g = 0 := hg
  have := DFunLike.congr_fun (comp_aeval (fun p => (C (y p) * X p.1 : MvPolynomial K Ω))
    (eval fun _ : K => (1 : Ω)).toIntAlgHom) g
  simp only [AlgHom.comp_apply] at this
  have h1 := ((congrArg (eval fun _ : K => (1 : Ω)).toIntAlgHom h0).symm.trans this).symm
  simp only [RingHom.toIntAlgHom_apply, map_mul, eval_C, eval_X, mul_one, map_zero] at h1
  exact h1

open Cardinal in

theorem exists_emb (L₀ : Type) [Field L₀] [CharZero L₀] (hK : #L₀ ≤ 𝔠) : Nonempty (L₀ →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ L₀)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : L₀ →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ L₀) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

theorem exists_pt [CharZero Ω] (y : (Σ k, ι k) → Ω) (hb : Birational y) (hr : IsRelevant (mCoordIdeal y))
    {w : MRing ι} (hw : Small.IsFormOff (mCoordIdeal y) w) : ∃ z ∈ mcPts (mCoordIdeal y), aeval z w ≠ 0 := by
  have hs : Function.Surjective fun q : MRing ι × MRing ι => aeval y q.1 / aeval y q.2 := fun s => by
    obtain ⟨_, g, h, -, -, h1, h2⟩ := hb s
    exact ⟨(g, h), by simp [h2, h1]⟩
  have hc : Cardinal.mk (MRing ι) ≤ Cardinal.aleph0 :=
    MvPolynomial.cardinalMk_le_max_lift.trans (by simp [-Cardinal.mk_fintype, -Cardinal.mk_sigma])
  haveI : Countable (MRing ι) := Cardinal.mk_le_aleph0_iff.1 hc
  haveI : Countable Ω := hs.countable
  obtain ⟨j⟩ := exists_emb Ω (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
  have ev : ∀ g : MRing ι, aeval (fun p => j (y p)) g = j (aeval y g) := fun g =>
    (DFunLike.congr_fun (comp_aeval y j.toIntAlgHom) g).symm
  refine ⟨fun p => j (y p), ⟨fun k => ?_, fun f hf => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hr k
    refine ⟨i, fun h0 => hi ?_⟩
    have : y ⟨k, i⟩ = 0 := (map_eq_zero j).1 h0
    simp [mCoordIdeal, RingHom.mem_ker, mConeMap, this]
  · rw [eval_map]
    exact (ev f).trans (by rw [aeval_of_mem y hf, map_zero])
  · obtain ⟨⟨d, hd⟩, hP⟩ := hw
    rw [ev]
    intro h0
    refine hP ?_
    show mConeMap y w = 0
    rw [cone_form y hd, (map_eq_zero j).1 h0, map_zero, mul_zero]

theorem val_int (y : (Σ k, ι k) → Ω) (n : ℤ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (v : ℂ) :
    Small.HasVal y 0 (n : Ω) z v ↔ v = n := by
  constructor
  · rintro ⟨dg, dh, g, h, hg, hh, hd, h1, h2, h3⟩
    obtain rfl : dg = dh := funext fun k => by simpa using hd k
    have hm : g - (n : MRing ι) * h ∈ mCoordIdeal y := by
      show mConeMap y _ = 0
      rw [map_sub, map_mul, cone_form y hg, cone_form y hh, h1, map_intCast, map_mul, map_intCast]; ring
    have := hz.2 _ hm
    rw [eval_map] at this
    have h4 : aeval z (g - (n : MRing ι) * h) = 0 := this
    rw [map_sub, map_mul, map_intCast, h3, ← sub_mul] at h4
    exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_right h2)
  · rintro rfl
    have hC : ∀ a : ℤ, IsMultiHomog (C a : MRing ι) 0 := fun a m hm k => by
      classical
      have : m = 0 := by simpa using support_monomial_subset hm
      simp [this]
    exact ⟨0, 0, C n, C 1, hC n, hC 1, by simp, by simp, by simp, by simp⟩

end Cone


end GlobalTheory.CompanionTheory.Ar.Plug.Test
