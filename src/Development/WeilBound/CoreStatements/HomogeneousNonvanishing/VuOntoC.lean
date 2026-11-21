import Development.WeilBound.CoreStatements.ProjectiveValuations.FrequentlyNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEvenSecEvRNeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorInvLePowHolomorphicOrbitPeriodBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToroidalFlagSmoothProjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexSectionFiniteCombination
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicExtensionSectionReading

section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt DifferentiableLines

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.VuOnto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open Limits GlobalTheory.CxPts Filter Topology

def Tw (V : Unf Xo c σ r) (e : Ix D → ℤ) (k : V.Comp) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ (a a₀ : (E →+* ℂ) × ℕ → ℕ) (n n₀ : ℕ) (g : Rul Xo c), Dom a n ∧ NV Xo c σ a n ∧ Dom a₀ n₀ ∧
    g ∈ sec Xo c a₀ n₀ ∧ (fun i => (ex D a n i : ℤ)) = e + (fun i => (ex D a₀ n₀ i : ℤ)) ∧
    laU V a n k = la + laU V a₀ n₀ k ∧ evR Xo c g y ≠ 0

theorem isSec_mul {X : Data E r} {la la' : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    (hQ : X.IsSec la' Q) : X.IsSec (la + la') (fun x => P x * Q x) := by
  refine ⟨hP.1.mul hQ.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hdiag : ∀ τ i, b τ i i ≠ 0 := fun τ i => by
      have hdet := (hb τ).1
      rw [Matrix.det_of_isUpperTriangular (M := mat b τ) (fun a c hac => (hb τ).2 a c hac)] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
    have hadd : bchar (la + la') b = bchar la b * bchar la' b := by
      simp only [bchar, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
      rw [Pi.add_apply, Pi.add_apply, zpow_add₀ (hdiag τ i)]
    show P _ * Q _ = _ * (P x * Q x)
    rw [hP.2.1 x hx b hb, hQ.2.1 x hx b hb, hadd]
    ring
  · show P _ * Q _ = _ * (P x * Q x)
    rw [hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx, X.χ_add la la' γ hγ]
    ring

theorem sec_frBorZ {V : Unf Xo c σ r} (hU : IsUnf V) {e : Ix D → ℤ} {k : V.Comp}
    {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la) {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P)
    {x x' : (V.X k).dom} {t : Ix D → (CAt σ)ˣ} (ht : FrBor t (V.un k x) (V.un k x')) :
    P x'.1 = chr e t * P x.1 := by
  obtain ⟨a, a₀, n, n₀, g, hD, hN, hD₀, hg, he, hl, hg0⟩ := hT (V.un k x)
  have hPg := isSec_mul hP (hU.2.2.2.2.1 a₀ n₀ hD₀ g hg k)
  rw [← hl] at hPg
  have h1 : P x'.1 * rdU V g k x'.1 = chr (fun i => (ex D a n i : ℤ)) t * (P x.1 * rdU V g k x.1) :=
    sec_frBor hU hD hN hPg ht
  rw [rdU_eq, rdU_eq, DifferentiableLines.evR_frBor hg ht, he, chr_add] at h1
  refine mul_right_cancel₀ (mul_ne_zero (chr_ne_zero (fun i => (ex D a₀ n₀ i : ℤ)) t)
    (show toC (evR Xo c g (V.un k x)) ≠ 0 from hg0)) ?_
  rw [h1]
  ring

theorem open_secZ {V : Unf Xo c σ r} (hU : IsUnf V) (T : TorFlag Xo c) {e : Ix D → ℤ} {k : V.Comp}
    {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la) {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P) :
    ∃ h ∈ GlobalTheory.CxPts.fibSec (flagStr T.X) σ (T.X.LL e), Reads V T e k P h ∧ OffZero V T k h := by
  classical
  obtain ⟨-, g1, g2, g3⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  have hex : ∀ (i : T.X.F.J) (z : Sp (CAt σ) ⟶ T.X.YY), ∃ v : ℂ,
      (∀ (x : (V.X k).dom) (hz : ⊤ ≤ z ⁻¹ᵁ T.X.F.U i) (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        T.X.F.ChartFr i z hz Q → FrBor t Q (V.un k x) → P x.1 = chr e t * v) ∧
      ((¬ ⊤ ≤ z ⁻¹ᵁ T.X.F.U i ∨ ∀ x : (V.X k).dom, T.X.ptY (V.un k x) ≠ z) → v = 0) := by
    intro i z
    by_cases h : ∃ (x : (V.X k).dom) (hz : ⊤ ≤ z ⁻¹ᵁ T.X.F.U i) (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        T.X.F.ChartFr i z hz Q ∧ FrBor t Q (V.un k x)
    · obtain ⟨x₀, hz₀, Q₀, t₀, hQ₀, ht₀⟩ := h
      refine ⟨(chr e t₀)⁻¹ * P x₀.1, fun x hz Q t hQ ht => ?_, fun h => ?_⟩
      · obtain rfl : Q₀ = Q := hQ₀.unique hQ
        have h1 := sec_frBorZ hU hT hP (g1 _ _ _ _ _ (g2 _ _ _ ht₀) ht)
        have h2 : chr e t = chr e t₀ * chr e (t₀⁻¹ * t) := by rw [← chr_mul, mul_inv_cancel_left]
        rw [h1, h2]
        have := chr_ne_zero e t₀
        field_simp
        try exact mul_comm _ _
      · exact (h.elim (fun h => h hz₀) fun h =>
          h x₀ (GlobalTheory.FlagMod.FlagCover.eq_ptY (hQ₀.lies.frBor ht₀)).symm).elim
    · exact ⟨0, fun x hz Q t hQ ht => (h ⟨x, hz, Q, t, hQ, ht⟩).elim, fun _ => rfl⟩
  choose v hv hv0 using hex
  refine ⟨fun i y => v i y.1, ⟨fun i j y hi hj => ?_, fun i y hi => hv0 i y.1 (Or.inl hi)⟩,
    fun x hx i y hz Q t _ hQ ht => hv i y.1 ⟨x, hx⟩ hz Q t hQ ht,
    fun i y h => hv0 i y.1 (Or.inr fun x => h x.1 x.2)⟩
  by_cases h : ∃ x : (V.X k).dom, T.X.ptY (V.un k x) = y.1
  · obtain ⟨x, hx⟩ := h
    obtain ⟨Q, t, hQ, ht⟩ := exists_chart_frBor T (V.un k x) i hx hi
    obtain ⟨Q', t', hQ', ht'⟩ := exists_chart_frBor T (V.un k x) j hx hj
    have hh : ⊤ ≤ (y.1 : Sp (CAt σ) ⟶ T.X.YY) ⁻¹ᵁ (T.X.F.U i ⊓ T.X.F.U j) := GlobalTheory.FlagMod.le_preimage_inf hi hj
    have h1 := g3 _ _ _ _ ht (g1 _ _ _ _ _ (hQ.frBor hQ' hh) ht')
    have h2 := (hv i y.1 x hi Q t hQ ht).symm.trans (hv j y.1 x hj Q' t' hQ' ht')
    have h3 : GlobalTheory.CxPts.gv (flagStr T.X) σ (T.X.LL e) i j y = chr (-e) (T.X.F.TAt (S := CAt σ) i j y.1 hh) :=
      (GlobalTheory.CxPts.ev_eq (p := flagStr T.X) (σ := σ) (y := y) (U := T.X.F.U i ⊓ T.X.F.U j) hh _).trans
        (T.X.F.ev_LL_g (S := CAt σ) e i j y.1 hh)
    have h4 : chr (-e) (T.X.F.TAt (S := CAt σ) i j y.1 hh) * chr e (T.X.F.TAt (S := CAt σ) i j y.1 hh) = 1 := by
      rw [← chr_add, neg_add_cancel, chr_zero]
    rw [h1, chr_mul] at h2
    show v i y.1 = _ * v j y.1
    rw [h3]
    refine mul_left_cancel₀ (chr_ne_zero e t') ?_
    linear_combination (chr (-e) (T.X.F.TAt (S := CAt σ) i j y.1 hh)) * h2 - chr e t' * v i y.1 * h4
  · push Not at h
    show v i y.1 = _ * v j y.1
    rw [hv0 i y.1 (Or.inr h), hv0 j y.1 (Or.inr h), mul_zero]

theorem differentiableAt_readsZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {e : Ix D → ℤ} {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la)
    {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P)
    {h : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T e k P h) (hZ : OffZero V T k h) (i : T.X.F.J) {m : ℕ}
    {B : Set (Fin m → ℂ)} (s : (Fin m → ℂ) → GlobalTheory.CxPts (flagStr T.X) σ)
    (ho : ∀ W, IsOpen (B ∩ s ⁻¹' ptsIn _ σ W))
    (hd : ∀ W (u : Γ(T.X.YY, W)), DifferentiableOn ℂ (fun b => ev _ σ W u (s b)) (B ∩ s ⁻¹' ptsIn _ σ W))
    {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) (hi : s b₀ ∈ ptsIn _ σ (flagOpen T.X ⊓ T.X.F.U i)) :
    DifferentiableAt ℂ (fun b => h i (s b)) b₀ := by
  obtain ⟨hO, hz⟩ := mem_ptsIn_inf.1 hi
  obtain ⟨Q₀, hQ₀⟩ := exists_chartFr_alg T (S := CAt σ) (zOf (s b₀)) hO (s b₀).2 i hz
  obtain ⟨a, a₀, n, n₀, g, hD, hN, hD₀, hg, he, hl, hg0⟩ := hT Q₀
  have hPg := isSec_mul hP (hU.2.2.2.2.1 a₀ n₀ hD₀ g hg k)
  rw [← hl] at hPg
  choose u hu using fun j => exists_fun_chart (σ := σ) T hg j
  let h' : T.X.F.J → GlobalTheory.CxPts (flagStr T.X) σ → ℂ := fun j y => h j y * ev _ σ _ (u j) y
  have hR' : Reads V T (fun i => (ex D a n i : ℤ)) k (fun x => P x * rdU V g k x) h' := by
    intro x hx j y hy Q t hxy hQ ht
    have e₁ : P x = chr e t * h j y := hR x hx j y hy Q t hxy hQ ht
    have e₂ : rdU V g k x = _ := (rdU_eq V g k ⟨x, hx⟩).trans (DifferentiableLines.evR_frBor hg ht)
    rw [hu j y hy Q (mem_open_of_ptY T _ _ hxy) hQ] at e₂
    show P x * rdU V g k x = chr (fun i => (ex D a n i : ℤ)) t * (h j y * ev _ σ _ (u j) y)
    rw [e₁, e₂, he, chr_add]
    ring
  have hZ' : OffZero (e := fun i => (ex D a n i : ℤ)) V T k h' := fun j y hy => by
    show h j y * _ = 0
    rw [hZ j y hy, zero_mul]
  have d₁ : DifferentiableAt ℂ (fun b => h' i (s b)) b₀ :=
    differentiableAt_reads hσ hU T hD hN hPg hR' hZ' i s ho hd hb₀ hi
  have d₂ : DifferentiableAt ℂ (fun b => ev _ σ _ (u i) (s b)) b₀ :=
    (hd _ (u i)).differentiableAt ((ho _).mem_nhds ⟨hb₀, hi⟩)
  have n₂ : ev _ σ _ (u i) (s b₀) ≠ 0 := by
    rw [← hu i _ hz Q₀ hO hQ₀]
    exact hg0
  refine (d₁.mul (d₂.inv n₂)).congr_of_eventuallyEq ?_
  filter_upwards [d₂.continuousAt.eventually_ne n₂] with b hb
  exact (mul_inv_cancel_right₀ hb _).symm

theorem open_holoZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {e : Ix D → ℤ} {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la)
    {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P) {d : ℕ} (R : GlobalTheory.AnRead (flagStr T.X) σ d)
    {h : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T e k P h) (hZ : OffZero V T k h) :
    ∀ i, R.HoloOn (ptsIn _ σ ((T.X.LL e).U i) ∩ ptsIn _ σ (flagOpen T.X)) (h i) := by
  intro i j v hv
  let C := R.chart j
  let L := EuclideanSpace.equiv (Fin d) ℂ
  have key := differentiableAt_readsZ hσ hU T hT hP hR hZ i (B := L.symm ⁻¹' C.e.target)
    (fun b => C.e.symm (L.symm b))
    (fun W => (GlobalTheory.ChartGlue.isOpen_over C.e (isOpen_ptsIn W)).preimage L.symm.continuous)
    (fun W u => (C.holo W u).comp L.symm.differentiableOn fun b hb => hb) (b₀ := L v)
    (by simpa using hv.1) (by
      simp only [ContinuousLinearEquiv.symm_apply_apply]
      exact mem_ptsIn_inf.2 ⟨hv.2.2, hv.2.1⟩)
  refine DifferentiableAt.differentiableWithinAt ?_
  have := key.comp v L.differentiableAt
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem evR_mul' (f g : Rul Xo c) (y : FrPt Xo c (CAt σ)) : evR Xo c (f * g) y = evR Xo c f y * evR Xo c g y :=
  evalAt_mul _ _ _ _ _

theorem evR_pow_ne {f : Rul Xo c} {y : FrPt Xo c (CAt σ)} (h : toC (evR Xo c f y) ≠ 0) (N : ℕ) :
    toC (evR Xo c (f ^ (N + 1)) y) ≠ 0 := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    rw [pow_succ, evR_mul']
    exact mul_ne_zero (M₀ := ℂ) ih h

open GlobalTheory.AllWt GlobalTheory.ShFam in

theorem tw_of_dec {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (κ : KeySec Xo c)
    (hNV : ∀ a n, Dom a n → NV Xo c σ a n) (G : WTZ E) (hG : G.2 = 0)
    (hdec : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < D.mult τ → G.1 (τ, j) ≤ G.1 (τ, i)) (k : V.Comp) :
    Tw V (exZ D G) k (modelWt V G k) := by
  intro y
  set M : ℕ := ∑ τ : E →+* ℂ, ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs with hM
  have hMb : ∀ (τ : E →+* ℂ) (i : ℕ), i < D.mult τ → -G.1 (τ, i) ≤ M := fun τ i hi => by
    have h1 : (G.1 (τ, i)).natAbs ≤ ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs :=
      Finset.single_le_sum (f := fun i => (G.1 (τ, i)).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 hi)
    have h2 : ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs ≤ M :=
      Finset.single_le_sum (f := fun τ => ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    have h3 : -G.1 (τ, i) ≤ ((G.1 (τ, i)).natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact neg_le_abs _
    omega
  obtain ⟨n₁, hn0, ⟨m', hm'⟩, h, hh, h0⟩ := GlobalTheory.Reg.exists_even_sec_evR_ne_zero E H D l Xo c σ y
  obtain ⟨m, rfl⟩ : ∃ m, n₁ = 2 * (m + 1) := ⟨m' - 1, by omega⟩
  set g : Rul Xo c := h ^ (M + 1) * (κ.ρ : Rul Xo c) ^ (M + 1) with hgdef
  have hh' : h ∈ secZ Xo c (fun i => (ex D 0 (2 * (m + 1)) i : ℤ)) := by
    rw [secZ_nat]; exact hh
  have hg0 := mul_mem_secZ (GlobalTheory.FlatTw.Hol.pow_succ_mem_secZ hh' M) (GlobalTheory.FlatTw.Hol.pow_succ_mem_secZ κ.mem M)
  have hg : g ∈ sec Xo c (fun _ => M + 1) (2 * ((M + 1) * m)) := by
    rw [← secZ_nat]
    convert hg0 using 2
    funext i
    rcases i with _ | ⟨τ, i⟩
    · simp [ex, keyEx]
      ring
    · simp [ex, keyEx]
  set a : (E →+* ℂ) × ℕ → ℕ := fun x => if x.2 < D.mult x.1 then (G.1 x + (M + 1)).toNat else 0 with ha
  have haZ : ∀ (τ : E →+* ℂ) (i : ℕ), i < D.mult τ → (a (τ, i) : ℤ) = G.1 (τ, i) + (M + 1) := fun τ i hi => by
    show ((if i < D.mult τ then (G.1 (τ, i) + (M + 1)).toNat else 0 : ℕ) : ℤ) = _
    rw [if_pos hi, Int.toNat_of_nonneg (by linarith [hMb τ i hi])]
  have hDa : Dom a (2 * ((M + 1) * m)) := by
    refine ⟨fun τ i j hij => ?_, even_two_mul _⟩
    simp only [ha]
    split_ifs with h1 h2 h2
    · exact Int.toNat_le_toNat (by linarith [hdec τ i j hij h1])
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have hEx : exZ D (wtZ a (2 * ((M + 1) * m))) = exZ D (G + wtZ (fun _ => M + 1) (2 * ((M + 1) * m))) := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · simp only [exZ, wtZ, Prod.snd_add, hG, zero_add]
    · simp [exZ, wtZ]
      exact haZ τ i i.2
  have hκ : toC (evR Xo c (κ.ρ : Rul Xo c) y) ≠ 0 := fun hz => by
    have e₁ : evR Xo c (κ.ρ : Rul Xo c) y * evR Xo c ((κ.ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) y = 1 := by
      rw [← evR_mul', Units.mul_inv]
      exact evalAt_one _ _ _ ((GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c).1.test _ _)
    have e₂ : toC (evR Xo c (κ.ρ : Rul Xo c) y) * toC (evR Xo c ((κ.ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) y) = 1 := e₁
    rw [hz, zero_mul] at e₂
    exact zero_ne_one e₂
  refine ⟨a, fun _ => M + 1, _, _, g, hDa, hNV _ _ hDa, ⟨fun _ => antitone_const, even_two_mul _⟩, hg, ?_, ?_, ?_⟩
  · rw [← GlobalTheory.AllWt.exZ_wtZ, ← GlobalTheory.AllWt.exZ_wtZ, hEx]
    exact funext fun i => by first | exact Formalism.L2.Pj.exZ_add _ _ i | exact GlobalTheory.AllWt.exZ_add _ _ i | (cases i <;> rfl)
  · rw [← modelWt_wtZ, modelWt_congr V hσ hU hEx, modelWt_add V (hG ▸ Even.zero)
      ⟨(((M + 1) * m : ℕ) : ℤ), by simp [wtZ]; ring⟩, modelWt_wtZ]
  · rw [hgdef, evR_mul']
    exact mul_ne_zero (M₀ := ℂ) (evR_pow_ne h0 M) (evR_pow_ne hκ M)

end PositivityTheory.UnitarySelfGeneration.VuOnto
end
end

section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt DifferentiableLines

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.VuOnto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

section ThetaShiftProofs

open Limits GlobalTheory.CxPts Filter Topology GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 800000 in

theorem tendsto_arc_readsZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {ee : Ix D → ℤ} (hee : ee none = 0) {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r}
    {P : Frame (V.X k).Ψ r → ℂ} (hP : P ∈ (V.X k).SS la)
    {h : (T.X.LL ee).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T ee k P h) (hZ : OffZero V T k h) (i : T.X.F.J)
    {W : T.X.YY.Opens} (hW : IsAffineOpen W) [IsDomain Γ(T.X.YY, W)] (hWi : W ≤ T.X.F.U i)
    (s : ℂ → GlobalTheory.CxPts (flagStr T.X) σ) {ρ : ℝ} (hρ : 0 < ρ) (hsW : ∀ u ∈ Metric.ball (0 : ℂ) ρ, s u ∈ ptsIn _ σ W)
    (hsd : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun u => ev _ σ W f (s u)) (Metric.ball 0 ρ))
    (h0 : s 0 ∉ ptsIn _ σ (flagOpen T.X)) (h1 : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → s u ∈ ptsIn _ σ (flagOpen T.X)) :
    Tendsto (fun u => h i (s u)) (𝓝[≠] 0) (𝓝 0) := by
  classical
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  let A : Type := Γ(T.X.YY, W)
  let q : Sp A ⟶ T.X.YY := GlobalTheory.FlagMod.tau hW
  let φ : c.F →+* A := (GlobalTheory.FlagMod.ev (q ≫ flagStr T.X) ⊤ le_top).comp (toΓ c.F)
  have hφ : q ≫ flagStr T.X = spMap φ := (GlobalTheory.FlagMod.spMap_ev_top _).symm
  have hz : ⊤ ≤ q ⁻¹ᵁ T.X.F.U i := GlobalTheory.FlagMod.tau_le hW hWi
  have hxc : (q ≫ T.X.π) ≫ T.Y.s = spMap φ ≫ spMap (RingHom.id c.F) :=
    ((Category.assoc _ _ _).trans hφ).trans ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (Spec.map_id _).symm))
  let x : Sp A ⟶ gen T.Y := pullback.lift _ _ hxc
  have hx : q ≫ T.X.π = x ≫ genι T.Y := (pullback.lift_fst _ _ _).symm
  have hxs : x ≫ genStr T.Y = spMap φ := pullback.lift_snd _ _ _
  obtain ⟨fr, hfr⟩ := exists_eigFrame_tau T hW hφ i hz hx
  have hb0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  let ψ : ℂ → (A →+* ℂ) := fun u => if hu : u ∈ Metric.ball (0 : ℂ) ρ then
    GlobalTheory.FlagMod.ev (s u).1 W (hsW u hu) else GlobalTheory.FlagMod.ev (s 0).1 W (hsW 0 hb0)
  have hψ : ∀ u (hu : u ∈ Metric.ball (0 : ℂ) ρ), ψ u = GlobalTheory.FlagMod.ev (s u).1 W (hsW u hu) := fun u hu => dif_pos hu
  have hψq : ∀ u ∈ Metric.ball (0 : ℂ) ρ, spMap (ψ u) ≫ q = (s u).1 := fun u hu => by
    rw [hψ u hu]
    exact GlobalTheory.FlagMod.spMap_ev (s u).1 hW _
  have hφu : ∀ u ∈ Metric.ball (0 : ℂ) ρ, (ψ u).comp φ = σ := fun u hu => by
    have e₁ : spMap ((ψ u).comp φ) = spMap (ψ u) ≫ spMap φ := Spec.map_comp _ _
    rw [← hφ, ← Category.assoc, hψq u hu, (s u).2] at e₁
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e₁)
  have key : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ∀ p : Sp ℂ,
      (s u).1 p ∈ flagOpen T.X ↔ (spMap (ψ u) ≫ x) p ∉ genBd T.Y := by
    intro u hu p
    have := GlobalTheory.LogKS.isIso_fst T.Y
    have e : (s u).1 p ∈ flagOpen T.X ↔ genι T.Y ((spMap (ψ u) ≫ x) p) ∈ Set.range T.Y.j := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hx, ← Category.assoc, hψq u hu]
      exact Iff.rfl
    rw [e, mem_genBd, not_not]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (genι T.Y).isOpenEmbedding.injective (by rw [← ha]; rfl)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← ha]; rfl⟩
  have hb : IsBdArc T.Y σ φ x ψ ρ := by
    refine ⟨⟨⟨hρ, fun f => (hsd f).congr fun u hu => ?_⟩, hxs, hφu⟩, fun p => ?_,
      fun u hu hne p => (key u hu p).1 (h1 u hu hne (Set.mem_univ p))⟩
    · rw [hψ u hu]
      exact (ev_eq (hsW u hu) f).symm
    · by_contra hp
      refine h0 (mem_ptsIn.2 ?_)
      rw [Subsingleton.elim (α := PrimeSpectrum ℂ) (IsLocalRing.closedPoint ℂ) p]
      exact (key 0 hb0 p).2 hp
  have hy' : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) ρ ∧ u ≠ 0 → ∃ y : FrPt Xo c (CAt σ), Matches fr (ψ u) y :=
    fun u hu => GlobalTheory.ShFam.BdArc.exists_matches E H D l Xo c c.F (RingHom.id c.F) T.Y σ _ φ x fr (ψ u) hxs
      (hφu u hu.1) (hb.2.2 u hu.1 hu.2)
  have hr : ((ρ / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ρ ∧ ((ρ / 2 : ℝ) : ℂ) ≠ 0 := by
    refine ⟨?_, by exact_mod_cast (half_pos hρ).ne'⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos hρ).le]
    exact half_lt_self hρ
  have : Nonempty (FrPt Xo c (CAt σ)) := ⟨(hy' _ hr).choose⟩
  choose! y hy using hy'
  have hm : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → Matches fr (ψ u) (y u) := fun u hu hne => hy u ⟨hu, hne⟩
  obtain ⟨k', T₀, M₀, γ₀, xx, hT, hO₀, hL⟩ :=
    GlobalTheory.T.exists_holomorphicFrameOrbit_lift_of_arc E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y hσ hU hb.1 hm
  have hne0 : ∀ w, eTwoPi w ≠ 0 := fun w => Complex.exp_ne_zero _
  have hi : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ⊤ ≤ zOf (s u) ⁻¹ᵁ T.X.F.U i := fun u hu => ptsIn_mono hWi (hsW u hu)
  have hfb : ∀ w (hw : T₀ < w.im), ∃ (hd : xx w ∈ (V.X k').dom) (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
      T.X.F.ChartFr i (zOf (s (eTwoPi w))) (hi _ (hT w hw)) Q ∧ FrBor t Q (V.un k' ⟨_, hd⟩) ∧ ∀ s, t (some s) = 1 := by
    intro w hw
    obtain ⟨hd, hl⟩ := hL w hw
    exact ⟨hd, exists_frBor_of_matches T q i hz hx fr hfr (ψ _)
      (matches_of_sameLie (hm _ (hT w hw) (hne0 w)) hl) (hψq _ (hT w hw)) _⟩
  have hev : ∀ᶠ w in imTop, T₀ < w.im := (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop _)
  refine tendsto_punctured ?_
  by_cases hk : k' = k
  swap
  · refine tendsto_const_nhds.congr' (hev.mono fun w hw => (hZ i _ fun x' hx' e => hk ?_).symm)
    obtain ⟨hd, Q, t, hQ, ht, -⟩ := hfb w hw
    have e' : T.X.ptY (V.un k ⟨x', hx'⟩) = zOf (s (eTwoPi w)) := e
    have hlx : T.X.F.Lies (zOf (s (eTwoPi w))) (V.un k ⟨x', hx'⟩) := e' ▸ T.X.lies_ptY _
    obtain ⟨t', ht'⟩ := hQ.exists_frBor hlx
    obtain ⟨γ, -, β, -, h'⟩ := (hU.2.2.2.1 k' k _ _).1 ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩
    exact (Sigma.mk.inj h').1.symm
  subst hk
  obtain ⟨M, γ, hO, hγ⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two E r _ T₀ M₀ γ₀ xx hO₀
  have hne : γ ≠ 1 := by
    rintro rfl
    obtain ⟨x₀, hx₀, x', a1, a2⟩ := GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain E r _ T₀ M xx hO
    exact GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ xx hσ hU hb hm hL x₀ hx₀ x' a1 a2
  obtain ⟨ξ, c', hξ, hc', ht⟩ := GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short E r _ T₀ M γ xx hO hγ hne
  obtain ⟨m, v, Lp, Lm, hlim⟩ := GlobalTheory.T.exists_arcLift_periods_tendsto_span E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ M γ xx hσ hU hb.1 hm hO hL
  have hper := GlobalTheory.T.eigenframe_specialization_uniform_bound E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ M γ xx hσ hU hb.1 hm hO hL
  obtain ⟨C', B, hn⟩ := GlobalTheory.T.normFactor_inv_le_pow_holomorphicOrbit_periodBound E r _ T₀ M γ xx la m v Lp Lm hO hlim hper
  have hp := tendsto_cusp hP hO.2.2.2.1 hξ hc' ht hn
  refine hp.congr' ?_
  filter_upwards [hev] with w hw
  obtain ⟨hd, Q, t, hQ, ht, ht1⟩ := hfb w hw
  have hu := hT w hw
  have e₁ : P (xx w) = chr ee t * h i (s (eTwoPi w)) :=
    hR (xx w) hd i _ (hi _ hu) Q t (GlobalTheory.FlagMod.FlagCover.eq_ptY (hQ.lies.frBor ht)).symm hQ ht
  rw [chr_of_some ht1, hee, zpow_zero, one_mul] at e₁
  exact e₁

end ThetaShiftProofs

open GlobalTheory.CxPts Filter Topology ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

set_option maxHeartbeats 800000 in

theorem holoOn_bdZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {ee : Ix D → ℤ} (hee : ee none = 0) {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r}
    {P : Frame (V.X k).Ψ r → ℂ} (hP : P ∈ (V.X k).SS la) {d : ℕ} [SmoothOfRelativeDimension d (flagStr T.X)]
    (R : GlobalTheory.AnRead (flagStr T.X) σ d)
    {h : (T.X.LL ee).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T ee k P h) (hZ : OffZero V T k h)
    (hh : ∀ i, R.HoloOn (ptsIn _ σ ((T.X.LL ee).U i) ∩ ptsIn _ σ (flagOpen T.X)) (h i))
    (i : T.X.F.J) :
    R.HoloOn (ptsIn _ σ (T.X.F.U i)) (h i) := by
  intro j v hv
  have hs : Smooth (flagStr T.X) := SmoothOfRelativeDimension.smooth d _
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ _ hs
  have := GlobalTheory.IsNormalScheme.of_pred hn
  let C := R.chart j
  let L := EuclideanSpace.equiv (Fin d) ℂ
  let y₀ := C.e.symm v
  obtain ⟨W₁, hyW₁, hW₁⟩ := GlobalTheory.ModelChart.exists_open_isDomain T.X.YY (y₀.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨W, hW, hyW, hWle⟩ := GlobalTheory.Points.exists_isAffineOpen_le y₀.1
    (mem_ptsIn_inf.2 ⟨mem_ptsIn.2 hyW₁, hv.2⟩ : y₀ ∈ ptsIn _ σ (W₁ ⊓ T.X.F.U i))
  have hyW' : y₀ ∈ ptsIn _ σ W := hyW
  have := hW₁ W (mem_ptsIn.1 hyW') (hWle.trans inf_le_left)
  have hWi := hWle.trans inf_le_right
  obtain ⟨p, hpW, hpO⟩ := (dense_flagOpen T.X).inter_open_nonempty W W.isOpen ⟨_, mem_ptsIn.1 hyW'⟩
  obtain ⟨g, hgO, hpg⟩ := hW.exists_basicOpen_le (V := flagOpen T.X) ⟨p, hpO⟩ hpW
  have hg : g ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hpg
    exact hpg
  let s : (Fin d → ℂ) → GlobalTheory.CxPts (flagStr T.X) σ := fun b => C.e.symm (L.symm b)
  have ho : ∀ {S}, IsOpen S → IsOpen (L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' S)) := fun hS =>
    (GlobalTheory.ChartGlue.isOpen_over C.e hS).preimage L.symm.continuous
  have hU' := ho (isOpen_ptsIn W)
  have hd : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun b => ev _ σ W f (s b))
      (L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' ptsIn _ σ W)) := fun f =>
    (C.holo W f).comp L.symm.differentiableOn fun _ hb => hb
  have key : DifferentiableAt ℂ (fun b => h i (s b)) (L v) := by
    refine differentiableAt_of_lines hU' (ho ((isOpen_ptsIn (T.X.F.U i)).inter (isOpen_ptsIn (flagOpen T.X)))) (hd g)
      (fun t ht h0 => ⟨ht.1, ptsIn_mono hWi ht.2, ptsIn_mono hgO ((mem_ptsIn_basicOpen ht.2 g).2 h0)⟩)
      ((hh i j).comp L.symm.differentiableOn fun _ hb => hb) (fun τ hτ hτO w hw => ?_)
      (by simpa using ⟨hv.1, hyW'⟩) fun ρ hρ => ?_
    · have hout : s τ ∉ ptsIn _ σ (flagOpen T.X) := fun h' => hτO ⟨hτ.1, ptsIn_mono hWi hτ.2, h'⟩
      have h0 : h i (s τ) = 0 := hZ i _ fun x hx e => hout (mem_open_of_ptY T _ _ e)
      have hline : Differentiable ℂ fun z : ℂ => τ + z • w := by fun_prop
      have hnb : ∀ᶠ z : ℂ in 𝓝 0, τ + z • w ∈ L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' ptsIn _ σ W) :=
        hline.continuous.continuousAt.preimage_mem_nhds (hU'.mem_nhds (by simpa using hτ))
      obtain ⟨ρ, hρ, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hnb.and (eventually_nhdsWithin_iff.1 hw))
      show Tendsto (fun z : ℂ => h i (s (τ + z • w))) _ (𝓝 (h i (s τ)))
      rw [h0]
      have b₁ : ∀ u ∈ Metric.ball (0 : ℂ) ρ, s (τ + u • w) ∈ ptsIn _ σ W := fun u hu => (hb u hu).1.2
      have b₂ : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun u : ℂ => ev _ σ W f (s (τ + u • w))) (Metric.ball 0 ρ) :=
        fun f => DifferentiableOn.comp (g := fun b => ev _ σ W f (s b)) (f := fun u : ℂ => τ + u • w) (hd f)
          hline.differentiableOn fun u hu => (hb u hu).1
      have b₃ : s (τ + (0 : ℂ) • w) ∉ ptsIn _ σ (flagOpen T.X) := by
        rw [zero_smul, add_zero]
        exact hout
      have b₄ : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → s (τ + u • w) ∈ ptsIn _ σ (flagOpen T.X) :=
        fun u hu hu0 => ((hb u hu).2 hu0).2.2
      exact tendsto_arc_readsZ hσ hU T hee hP hR hZ i hW hWi (fun z => s (τ + z • w)) hρ b₁ b₂ b₃ b₄
    · have hsrc : y₀ ∈ C.e.source := C.e.map_target hv.1
      have hc : ContinuousAt (fun y => L (C.e y)) y₀ := L.continuous.continuousAt.comp (C.e.continuousAt hsrc)
      have hN : {y | L (C.e y) ∈ Metric.ball (L v) ρ} ∈ 𝓝 y₀ :=
        hc.preimage_mem_nhds (by rw [C.e.right_inv hv.1]; exact Metric.ball_mem_nhds _ hρ)
      obtain ⟨y', hy', hne⟩ := frequently_ne_zero (flagStr T.X) hW hg hyW'
        (inter_mem hN (C.e.open_source.mem_nhds hsrc))
      refine ⟨_, hy'.1, ?_⟩
      simp only [s, ContinuousLinearEquiv.symm_apply_apply]
      rwa [C.e.left_inv hy'.2]
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (key.comp v L.differentiableAt).congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  simp only [s, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

end PositivityTheory.UnitarySelfGeneration.VuOnto
end
end

section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt DifferentiableLines

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.VuOnto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open GlobalTheory.CxPts

theorem exists_comb {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {e : Ix D → ℤ} (he : e none = 0) {la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : ∀ k, Tw V e k (la k))
    {P : ∀ k, Frame (V.X k).Ψ r → ℂ} (hP : ∀ k, P k ∈ (V.X k).SS (la k)) :
    ∃ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ extVanZ T.X e) ∧
      ∀ k, ∀ x ∈ (V.X k).dom, P k x = ∑ i, as i * rdU V (fs i) k x := by
  classical
  letI := V.fin
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  obtain ⟨d, hsm, hpr⟩ := GlobalTheory.T.toroidal_flag_smooth_projective E H D l Xo c T
  let R : GlobalTheory.AnRead (flagStr T.X) σ d := GlobalTheory.AnRead.all _ _ _
  choose hk hf hR hZ using fun k => open_secZ hU T (hT k) (hP k).1.1
  have hh : ∀ k, hk k ∈ R.holSec (T.X.LL e) := fun k =>
    ⟨hf k, holoOn_bdZ hσ hU T he (hP k) R (hR k) (hZ k) (open_holoZ hσ hU T (hT k) (hP k).1.1 R (hR k) (hZ k))⟩
  let h : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ := ∑ k, hk k
  have hh' : h ∈ R.holSec (T.X.LL e) := Submodule.sum_mem _ fun k _ => hh k
  have hap : ∀ (i : (T.X.LL e).ι) y, h i y = ∑ k, hk k i y := fun i y => by simp only [h, Finset.sum_apply]
  have hv : ∀ i y, y ∉ ptsIn (flagStr T.X) σ (flagOpen T.X) → h i y = 0 := fun i y hy => by
    simp only [h, Finset.sum_apply]
    exact Finset.sum_eq_zero fun k _ => hZ k i y fun x hx e' => hy (mem_open_of_ptY T _ _ e')
  have hRh : ∀ k, Reads V T e k (P k) h := fun k x hx i y hz Q t hxy hQ ht => by
    have e₁ : h i y = hk k i y := by
      refine (hap i y).trans (Finset.sum_eq_single k (fun k' _ hne => hZ k' i y fun x' hx' e' => hne ?_)
        fun h' => (h' (Finset.mem_univ _)).elim)
      have e'' : T.X.ptY (V.un k' ⟨x', hx'⟩) = zOf y := e'
      have hlx : T.X.F.Lies (zOf y) (V.un k' ⟨x', hx'⟩) := e'' ▸ T.X.lies_ptY _
      obtain ⟨t', ht'⟩ := GlobalTheory.FlagMod.Frames.ChartFr.exists_frBor (z := zOf y) hQ hlx
      obtain ⟨γ, -, β, -, h'⟩ := (hU.2.2.2.1 k k' _ _).1 ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩
      exact (Sigma.mk.inj h').1
    rw [e₁]
    exact hR k x hx i y hz Q t hxy hQ ht
  have hB := T.X.F.isLB_LL e
  obtain ⟨xC, hx⟩ := (GlobalTheory.AnRead.bijective_valC hpr R hB).2 ⟨h, hh'⟩
  have hxv : GlobalTheory.SecC.val xC = h := congrArg Subtype.val hx
  have hlft : LocallyOfFiniteType (flagStr T.X) := by
    haveI := hsm
    haveI : Smooth (flagStr T.X) := SmoothOfRelativeDimension.smooth d _
    infer_instance
  obtain ⟨m, as, ss, hss, hsum⟩ := GlobalTheory.T.complex_section_finite_combination c.F T.X.YY (flagStr T.X) σ hlft _ hB (flagOpen T.X) xC
    (fun i y hy => by rw [hxv]; exact hv i y hy)
  refine ⟨m, as, fun j => ruleTop T.X _ (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j)), fun j => ?_,
    fun k => GlobalTheory.T.holomorphic_extension_section_reading E H D l Xo c r σ V T e k (P k) h (hRh k) m as ss (hxv.symm.trans hsum)⟩
  refine ruleTop_mem_extVanZ.2 (mem_vanOut_iff_le.2 ?_)
  have e' : toSec (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j)) = ss j :=
    (Equiv.ofBijective _ GlobalTheory.Vanishing.H0.bijective_ofSec_top).symm_apply_apply (ss j)
  rw [e']
  exact hss j

end PositivityTheory.UnitarySelfGeneration.VuOnto
end
end
