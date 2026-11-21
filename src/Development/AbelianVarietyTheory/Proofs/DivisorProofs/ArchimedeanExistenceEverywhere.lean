import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPairQuotientHorizontalGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReadingStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnReadingIntegerExponentSectionStatement
import Formalism.LocalToGlobal.ProjectiveLattices.TieGenDense

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore Filter Topology

namespace GlobalTheory.FlatCore

theorem exists_ringHom_ne_zero_of_not_isNilpotent {K R : Type} [Field K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (σ : K →+* ℂ) {b : R} (hb : ¬ IsNilpotent b) :
    ∃ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ ∧ φ b ≠ 0 := by
  haveI hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hrad : b ∉ (⊥ : Ideal R).jacobson := by
    rw [← Ideal.radical_eq_jacobson]
    intro h
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 h
    exact hb ⟨n, by simpa using hn⟩
  rw [Ideal.jacobson, Submodule.mem_sInf] at hrad
  push_neg at hrad
  obtain ⟨m, ⟨-, hm⟩, hbm⟩ := hrad
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective _ _)
  haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  haveI : Algebra.IsAlgebraic K (R ⧸ m) := Algebra.IsAlgebraic.of_finite K (R ⧸ m)
  letI : Algebra K ℂ := σ.toAlgebra
  let ψ : (R ⧸ m) →ₐ[K] ℂ := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk m), ?_, ?_⟩
  · ext a
    show ψ (Ideal.Quotient.mkₐ K m (algebraMap K R a)) = σ a
    rw [AlgHom.commutes, AlgHom.commutes]
    rfl
  · show ψ (Ideal.Quotient.mk m b) ≠ 0
    rw [map_ne_zero_iff ψ ψ.toRingHom.injective]
    exact fun h => hbm (Ideal.Quotient.eq_zero_iff_mem.1 h)

theorem differentiableOn_of_mem_holSub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {C : Type}
    {X : C → Data E r} {la : ∀ k, Wt (X k).Ψ r} {P : FDSec X} (hP : P ∈ holSub X la) (k : C) :
    DifferentiableOn ℂ (P k) (X k).dom := by
  induction hP using Submodule.span_induction with
  | mem P h => exact (h k).1.1.1
  | zero => exact differentiableOn_const 0
  | add P Q _ _ hP hQ => exact hP.add hQ
  | smul a P _ hP => exact hP.const_smul a

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c}

theorem genVal_ne_zero_of_mem_cuspOn (hf : f ∈ cuspOn U Z G) (hf0 : f ≠ 0) : genVal Z f ≠ 0 := by
  have hG : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  intro h0
  refine hf0 (secZ_eq_zero_of_genVal (cuspW_le_secZ G (Submodule.mem_inf.1 hf).1) fun Z' => ?_)
  by_cases hZ : Z' = Z
  · rw [hZ]; exact h0
  · rw [genVal_apply hG]; exact evC_eq_zero hG hZ (Submodule.mem_inf.1 hf).2

theorem idem_mul_eq_zero_of_mul_eq_zero (hf : f ∈ cuspOn U Z G) (hf0 : f ≠ 0) {e' : Ix Dw → ℤ} {s : Rul Xo c}
    (hs : s ∈ secZ Xo c e') (hsf : s * f = 0) : idem Z * s = 0 := by
  have hG : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  have h1 : genVal Z s = 0 := by
    have h2 := congrArg (genVal Z) hsf
    rw [map_mul, map_zero] at h2
    exact (mul_eq_zero.1 h2).resolve_right (genVal_ne_zero_of_mem_cuspOn hf hf0)
  refine secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hs) fun Z' => ?_
  rw [map_mul]
  by_cases hZ : Z' = Z
  · rw [hZ, h1, mul_zero]
  · rw [genVal_apply hG Z' (idem Z), evC_eq_zero hG hZ (idem_mem_suppOn Z), zero_mul]

theorem exists_framesOn_rdU_ne_zero (hL : Laws U x) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (hf : f ∈ cuspOn U Z G)
    (hf0 : f ≠ 0) : ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f z.1 z.2 ≠ 0 := by
  have hfs : f ∈ secZ Xo c (exZ Dw G) := cuspW_le_secZ G (Submodule.mem_inf.1 hf).1
  obtain ⟨R, hR, t, hmem, hφ⟩ :=
    GlobalTheory.DegCmp.exists_chart_read_at_frames E H Dw l Xo c r σ (U σ) (hL.unf σ hσ) Z
  let b : R := ⟨_, hmem _ f hfs⟩
  have hb : ¬ IsNilpotent b := fun h => by
    have h2 : ((b : Om Z)) = 0 := by rw [h.eq_zero]; rfl
    exact genVal_ne_zero_of_mem_cuspOn hf hf0 ((mul_eq_zero.1 h2).resolve_left (Units.ne_zero _))
  obtain ⟨φ, hφσ, hφb⟩ := exists_ringHom_ne_zero_of_not_isNilpotent σ hb
  obtain ⟨z, hz, s, hread⟩ := hφ φ hφσ
  refine ⟨z, hz, fun h0 => hφb ?_⟩
  rw [hread _ f hfs b rfl, h0, mul_zero]

theorem rdU_eq_of_rdU_mul (hL : Laws U x) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (hf : f ∈ cuspOn U Z G)
    (hf0 : f ≠ 0) {e' : Ix Dw → ℤ} (he : e' none = 0) {s : Rul Xo c} (hs : s ∈ secZ Xo c e')
    (q : FDSec (U σ).X) (hq : ∀ k, ContinuousOn (q k) ((U σ).X k).dom)
    (hrel : ∀ z ∈ framesOn (U σ) Z, rdU (U σ) (s * f) z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) :
    ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 = q z.1 z.2 := by
  obtain ⟨k, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  have hex : ∃ y ∈ ((U σ).X k).dom, rdU (U σ) f k y ≠ 0 := by
    obtain ⟨⟨k₀, y₀⟩, hz₀, hne⟩ := exists_framesOn_rdU_ne_zero hL hσ hf hf0
    rw [hk] at hz₀
    obtain ⟨h1, hy₀⟩ := hz₀
    subst h1
    exact ⟨y₀, hy₀, hne⟩
  have hdiff : DifferentiableOn ℂ (rdU (U σ) f k) ((U σ).X k).dom :=
    differentiableOn_of_mem_holSub ((mem_cuspW.1 (Submodule.mem_inf.1 hf).1).2 σ hσ) k
  have hint := interior_closure_zero ((U σ).X k) hdiff hex
  have hcont : ContinuousOn (fun y => rdU (U σ) s k y - q k y) ((U σ).X k).dom :=
    (GlobalTheory.T.continuousOn_reading_integerExponent_section E H Dw l Xo c r U x hL e' he s hs σ hσ k).sub (hq k)
  have hO := FourierCoefficientDomain.isOpen_dom ((U σ).X k)
  have key : ∀ y ∈ ((U σ).X k).dom, rdU (U σ) s k y = q k y := by
    intro y hy
    by_contra hne
    have hev : ∀ᶠ w in 𝓝 y, rdU (U σ) s k w - q k w ≠ 0 ∧ w ∈ ((U σ).X k).dom :=
      ((hcont.continuousAt (hO.mem_nhds hy)).eventually_ne (sub_ne_zero.2 hne)).and (hO.mem_nhds hy)
    have hsub : {w | rdU (U σ) s k w - q k w ≠ 0 ∧ w ∈ ((U σ).X k).dom} ⊆
        closure {w | w ∈ ((U σ).X k).dom ∧ rdU (U σ) f k w = 0} := by
      rintro w ⟨hw, hwd⟩
      refine subset_closure ⟨hwd, ?_⟩
      have h3 := hrel ⟨k, w⟩ (by rw [hk]; exact ⟨rfl, hwd⟩)
      rw [GlobalTheory.AllWt.rdU_mul (U σ)] at h3
      have h2 : (rdU (U σ) s k w - q k w) * rdU (U σ) f k w = 0 := by
        rw [sub_mul, sub_eq_zero]
        exact h3
      exact (mul_eq_zero.1 h2).resolve_left hw
    have hy' : y ∈ interior (closure {w | w ∈ ((U σ).X k).dom ∧ rdU (U σ) f k w = 0}) :=
      interior_mono hsub (mem_interior_iff_mem_nhds.2 hev)
    rw [hint] at hy'
    exact hy'
  rintro ⟨k', y⟩ hz
  rw [hk] at hz
  obtain ⟨h1, hy⟩ := hz
  subst h1
  exact key y hy

theorem cuspOn_cancel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (G : WTZ E) (e' : Ix Dw → ℤ) (f s : Rul Xo c), f ∈ cuspOn U Z G → f ≠ 0 → s ∈ secZ Xo c e' → (s * f = 0 → idem Z * s = 0) ∧ (e' none = 0 → ∀ σ, GoodEmb c σ → ∀ (q : FDSec (U σ).X), (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) (s * f) z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 = q z.1 z.2) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z G e' f s hf hf0 hs
  exact ⟨idem_mul_eq_zero_of_mul_eq_zero hf hf0 hs,
    fun he σ hσ q hq hrel => rdU_eq_of_rdU_mul hL hσ hf hf0 he hs q hq hrel⟩

end GlobalTheory.FlatCore

end
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_section_annihilator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (G : WTZ E) (e' : Ix Dw → ℤ) (f s : Rul Xo c), f ∈ cuspOn U Z G → f ≠ 0 → s ∈ secZ Xo c e' → (s * f = 0 → idem Z * s = 0) ∧ (e' none = 0 → ∀ σ, GoodEmb c σ → ∀ (q : FDSec (U σ).X), (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) (s * f) z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 = q z.1 z.2) := by
  first | exact @GlobalTheory.FlatCore.cuspOn_cancel | exact GlobalTheory.FlatCore.cuspOn_cancel | (intros; apply GlobalTheory.FlatCore.cuspOn_cancel <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem archEx_continuous_det {r : ℕ} {Ψ : Finset (E →+* ℂ)} (τ : Ψ) :
    Continuous fun y : Frame Ψ r => (mat y τ).det :=
  Continuous.matrix_det (continuous_apply τ)

theorem archEx_continuousOn_horizGen {r : ℕ} (X : Data E r) (τ : X.Ψ) : ContinuousOn (horizGen τ) X.dom :=
  (archEx_continuous_det τ).continuousOn.inv₀ fun _ hy => (hy τ).1

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem archEx_relab_mem {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (τ : Psi H) (k : U.Comp) :
    relab c σ τ.1 ∈ (U.X k).Ψ := by
  refine ((hU.2.1 k).2 _).2 ?_
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  exact (congrArg σ (Subtype.ext τ.2)).trans hσ0

end SlopeTestRemainingChoices

theorem archEx_always : Always fun U x => ArchEx U x := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ
  obtain ⟨G, f, g, -, hf, hg, hf0, hq⟩ := GlobalTheory.T.exists_cuspForm_pair_quotient_horizontal_generator E H Dw l Xo c r U x hL Z τ
  have hfs : f ∈ secZ Xo c (exZ Dw G) := cuspW_le_secZ G hf.1
  have hgs : g ∈ secZ Xo c (exZ Dw (G + wtOf Dw (flatWt Dw τ) 0)) := cuspW_le_secZ _ hg.1
  have hex : exZ Dw (G + wtOf Dw (flatWt Dw τ) 0) - exZ Dw G = exOf Dw (flatWt Dw τ) 0 := by
    funext i; rw [Pi.sub_apply, exZ_add, exOf, add_sub_cancel_left]
  have hmem : ∀ σ (hσ : GoodEmb c σ) k, relab c σ τ.1 ∈ ((U σ).X k).Ψ := fun σ hσ k =>
    archEx_relab_mem (U σ) hσ (hL.unf σ hσ) τ k
  have hgood : ∀ σ, GoodEmb c (goodOf c σ) := fun σ => goodEmb_goodOf c σ
  have hσ₀ := hgood c.F.val.toRingHom
  generalize goodOf c c.F.val.toRingHom = σ₀ at hσ₀
  obtain ⟨a₀, ha₀, h₀⟩ := hq σ₀ hσ₀
  obtain ⟨sig, hsig, hsi, hsf⟩ := GlobalTheory.T.exists_section_quotient_of_continuous_reading E H Dw l Xo c r U x hL Z _ _ f g hfs hf.2 hgs hg.2 hf0 σ₀ hσ₀
    (fun k y => a₀ * horizGen ⟨_, hmem σ₀ hσ₀ k⟩ y)
    (fun k => continuousOn_const.mul (archEx_continuousOn_horizGen _ _)) (fun z hz => h₀ z.1 _ z.2 hz)
  rw [hex] at hsig
  have hrd : ∀ σ (hσ : GoodEmb c σ), ∃ a : ℂ, a ≠ 0 ∧ ∀ z ∈ framesOn (U σ) Z,
      rdU (U σ) sig z.1 z.2 = a * horizGen ⟨_, hmem σ hσ z.1⟩ z.2 := fun σ hσ => by
    obtain ⟨a, ha, h⟩ := hq σ hσ
    exact ⟨a, ha, (GlobalTheory.T.cusp_section_annihilator E H Dw l Xo c r U x hL Z G _ f sig hf hf0 hsig).2 rfl σ hσ
      (fun k y => a * horizGen ⟨_, hmem σ hσ k⟩ y)
      (fun k => continuousOn_const.mul (archEx_continuousOn_horizGen _ _))
      (fun z hz => hsf.symm ▸ h z.1 _ z.2 hz)⟩
  have hnorm : ∀ σ (hσ : GoodEmb c σ), ∃ b : ℝ, 0 < b ∧
      homN (U σ) x (wtOf Dw (flatWt Dw τ) 0) sig '' framesOn (U σ) Z = {b} := fun σ hσ => by
    obtain ⟨a, ha, h⟩ := hrd σ hσ
    obtain ⟨k, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
    obtain ⟨y, hy⟩ := GlobalTheory.CompBij.frames_nonempty ((U σ).X k)
    refine ⟨lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0) * (‖a‖ * Real.sqrt ‖relab c σ τ.1 ((U σ).X k).Gm.det‖),
      mul_pos (lieFacZ_pos _ _) (mul_pos (norm_pos_iff.2 ha) (Real.sqrt_pos.2 (norm_pos_iff.2
        ((map_ne_zero _).2 ((U σ).X k).Gm_det)))), image_eq_singleton_iff.2 ⟨⟨⟨k, y⟩, ?_⟩, ?_⟩⟩
    · rw [hk]; exact ⟨rfl, hy⟩
    · rintro ⟨k', y'⟩ hz
      have h1 := h _ hz
      have hz' := hz
      rw [hk] at hz'
      obtain ⟨rfl, hy'⟩ : k' = k ∧ y' ∈ ((U σ).X k').dom := hz'
      rw [← pnorm_horizGen ((U σ).X k') ⟨_, hmem σ hσ k'⟩ hy', homN, ptN,
        modelWt_flatWt (U σ) hσ (hL.unf σ hσ) τ k' (hmem σ hσ k')]
      simp only at h1
      simp only [Data.pnorm, h1, norm_mul, mul_assoc]
  have hg0 : g ≠ 0 := fun h0 => by
    have h1 : sig = 0 := hsi.symm.trans
      ((GlobalTheory.T.cusp_section_annihilator E H Dw l Xo c r U x hL Z G _ f sig hf hf0 hsig).1 (hsf.trans h0))
    obtain ⟨b, hb, h2⟩ := hnorm σ₀ hσ₀
    obtain ⟨⟨z, hz⟩, h3⟩ := image_eq_singleton_iff.1 h2
    have h4 := h3 z hz
    rw [h1, ← zero_smul c.F (0 : Rul Xo c), homN_smul, map_zero, norm_zero, zero_mul] at h4
    exact hb.ne h4
  obtain ⟨inv, hinv, hii, hig⟩ := GlobalTheory.T.exists_section_quotient_of_continuous_reading E H Dw l Xo c r U x hL Z _ _ g f hgs hg.2 hfs hf.2 hg0 σ₀ hσ₀
    (fun k y => a₀⁻¹ * (mat y ⟨_, hmem σ₀ hσ₀ k⟩).det)
    (fun k => (continuous_const.mul (archEx_continuous_det _)).continuousOn) (fun z hz => by
      have hd := (hz.1 ⟨_, hmem σ₀ hσ₀ z.1⟩).1
      rw [h₀ z.1 (hmem σ₀ hσ₀ z.1) z.2 hz, horizGen]
      field_simp)
  rw [← neg_sub, hex] at hinv
  have hif : idem Z * f = f := by rw [← hig, ← mul_assoc, hii]
  have hs0 : sig * inv - idem Z ∈ secZ Xo c 0 := by
    have := mul_mem_secZ hsig hinv
    rw [add_neg_cancel] at this
    exact Submodule.sub_mem _ this (idem_mem_secZ Z)
  have hone : sig * inv = idem Z := by
    have h1 := (GlobalTheory.T.cusp_section_annihilator E H Dw l Xo c r U x hL Z G _ f _ hf hf0 hs0).1 (by
      rw [sub_mul, hif, mul_right_comm, hsf, mul_comm, hig, sub_self])
    rwa [mul_sub, ← mul_assoc, hsi, idem_mul_idem, sub_eq_zero] at h1
  choose b hb hb' using fun σ => hnorm _ (hgood σ)
  exact ⟨⟨sig, inv, hsig, hinv, hsi, hii, hone, b, hb, hb'⟩⟩

end GlobalTheory.FlatCore

end
end
