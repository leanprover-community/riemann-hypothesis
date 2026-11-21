import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem exZ_zero_model : exZ Dw (0 : WTZ E) = 0 := by
  funext i; cases i <;> rfl

theorem mul_smul_idem_mem_cuspOn {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (a : c.F) :
    f * (a • idem Z) ∈ cuspOn U Z G := by
  have h : idem Z * f = f := idem_mul_eq (e := exZ Dw G) ⟨cuspW_le_secZ G hf.1, hf.2⟩
  rw [mul_smul_comm, mul_comm, h]
  exact Submodule.smul_mem _ _ hf

variable (x) in

def TwSec.constModel {Z : Comp Xo c} (h : HasPts U Z) (a : c.F) (ha : a ≠ 0) : TwSec U x Z 0 where
  even := ⟨0, rfl⟩
  sig := a • idem Z
  inv := a⁻¹ • idem Z
  sig_mem := by rw [exZ_zero_model]; exact Submodule.smul_mem _ _ (idem_mem_secZ Z)
  inv_mem := by rw [exZ_zero_model, neg_zero]; exact Submodule.smul_mem _ _ (idem_mem_secZ Z)
  idem_sig := by rw [mul_smul_comm, idem_mul_idem]
  idem_inv := by rw [mul_smul_comm, idem_mul_idem]
  mul_inv := (smul_mul_inv_smul ha _ _).trans (idem_mul_idem Z)
  cInf := fun σ => ‖σ a‖
  cInf_pos σ := norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  norm_inf σ z hz := by
    rw [homN_smul, homN_idem _ x hz.1 hz.2 ((h.1 σ).2 z hz _), norm_goodOf, mul_one]
  cusp_sig G _ f hf := by rw [add_zero]; exact mul_smul_idem_mem_cuspOn hf a
  cusp_inv G _ f hf := by rw [add_zero] at hf; exact mul_smul_idem_mem_cuspOn hf a⁻¹
  lo := fun w => (vAdd w a : ℝ)
  hi := fun w => (vAdd w a : ℝ)
  lo_le w v hv := by rw [(isVal_valOn hv).smul _ _ ha, val_idem hv, add_zero]
  le_hi w v hv := by rw [(isVal_valOn hv).smul _ _ ha, val_idem hv, add_zero]
  finite_lo := finite_vAdd ha
  finite_hi := finite_vAdd ha









theorem mem_holSub_model {Cp : Type} (X : Cp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) :
    P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

theorem isSec_inv (X : Data E r) {la la' : Wt X.Ψ r} (hla : la' + la = 0) {e s t : Frame X.Ψ r → ℂ}
    (he : X.IsSec 0 e) (ht : X.IsSec la t) (hee : e * e = e) (hes : e * s = s) (het : e * t = t) (hst : s * t = e) :
    X.IsSec la' s := by
  have ee : ∀ y, e y * e y = e y := congrFun hee
  have es : ∀ y, e y * s y = s y := congrFun hes
  have et : ∀ y, e y * t y = t y := congrFun het
  have st : ∀ y, s y * t y = e y := congrFun hst
  have e01 : ∀ y, e y = 0 ∨ e y = 1 := fun y => IsIdempotentElem.iff_eq_zero_or_one.1 (ee y)
  have key : ∀ y y' (a b : ℂ), b * a = 1 → e y' = e y → t y' = a * t y → s y' = b * s y := by
    intro y y' a b hab h1 h2
    have := es y; have := es y'; have := st y; have := st y'
    rcases e01 y with h | h
    · rw [← es y', ← es y, h1, h]; simp
    · have h3 := st y
      have h4 := st y'
      rw [h1, h2, h] at h4
      rw [h] at h3
      linear_combination (-s y') * h3 + (b * s y) * h4 - (s y' * s y * t y) * hab
  have hχ0 : ∀ γ ∈ X.Γ, X.χ 0 γ = 1 := fun γ hγ => by
    obtain ⟨n, hn, h⟩ := X.χ_fin 0
    have h1 := X.χ_add 0 0 γ hγ
    rw [add_zero] at h1
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 h1.symm with h2 | h2
    · have := h γ hγ
      rw [h2, zero_pow hn.ne'] at this
      exact absurd this zero_ne_one
    · exact h2
  refine ⟨?_, fun y hy b hb => key _ _ _ _ ?_ ?_ (ht.2.1 y hy b hb), fun γ hγ y hy => key _ _ _ _ ?_ ?_ (ht.2.2 γ hγ y hy)⟩
  · have hne : ∀ y, t y + 1 - e y ≠ 0 := fun y => by
      rcases e01 y with h | h
      · rw [← et y, h]; simp
      · have h3 := st y
        rw [h] at h3 ⊢
        intro h0
        have : t y = 0 := by linear_combination h0
        rw [this, mul_zero] at h3
        exact zero_ne_one h3
    have : s = fun y => e y * (t y + 1 - e y)⁻¹ := funext fun y => by
      rw [eq_mul_inv_iff_mul_eq₀ (hne y)]
      linear_combination st y - es y
    rw [this]
    exact he.1.fun_mul (((ht.1.add_const 1).fun_sub he.1).fun_inv fun y _ => hne y)
  · have hd : ∀ τ i, b τ i i ≠ 0 := fun τ i h0 => (hb τ).1 (by
      rw [Matrix.det_of_isUpperTriangular (M := mat b τ) (fun a c h => (hb τ).2 a c h)]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0)
    simp only [bchar, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_add₀ (hd τ i), show la' τ i + la τ i = 0 from congrFun (congrFun hla τ) i, zpow_zero]
  · rw [he.2.1 y hy b hb]; simp [bchar]
  · rw [← X.χ_add _ _ γ hγ, hla, hχ0 γ hγ]
  · rw [he.2.2 γ hγ y hy, hχ0 γ hγ, one_mul]

theorem mul_mem_cuspOn_of_isSec {Z : Comp Xo c} {G₀ : WTZ E} (h0 : Even G₀.2) {s : Rul Xo c}
    (hs : s ∈ secZ Xo c (exZ Dw G₀)) (hZ : s ∈ suppOn Z)
    (hh : ∀ σ, GoodEmb c σ → ∀ k, ((U σ).X k).IsSec (modelWt (U σ) G₀ k) (rdU (U σ) s k))
    (hb : ∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C)
    {G : WTZ E} (hG : Even G.2) {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : f * s ∈ cuspOn U Z (G + G₀) := by
  refine ⟨?_, mul_mem_suppOn _ hZ⟩
  have hf' := mem_cuspW.1 hf.1
  refine mem_cuspW.2 ⟨exZ_add_eq (Dw := Dw) G G₀ ▸ mul_mem_secZ hf'.1 hs, fun σ hσ => ?_⟩
  rw [AllWt.rdU_mul, mem_holSub_model]
  intro k
  rw [modelWt_add (U σ) hG h0 k]
  refine (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_model _ _ _).1 (hf'.2 σ hσ) k) _ ⟨hh σ hσ k, ?_⟩
  obtain ⟨C, hC⟩ := hb σ hσ
  refine ⟨max 0 (C / lieFacZ Dw x G₀), fun y _ => ?_⟩
  by_cases hy : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
  · refine le_max_of_le_right ((le_div_iff₀' (lieFacZ_pos x G₀)).2 ?_)
    have := hC _ hy
    unfold homN ptN at this
    exact this
  · have := rdU_eq_zero (U σ) hZ hy
    simp only at this
    simp [Data.pnorm, this]

theorem exists_twSec_of_dom (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {Z : Comp Xo c} {la : Weight Dw}
    {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ) (hδ : (Function.support δ).Finite)
    {a : (E →+* ℂ) × ℕ → ℕ} (ha : Dom a 0) (hla : exZ Dw (wtOf Dw (-la) 0) = exZ Dw (wtZ a 0)) :
    ∃ t : TwSec U x Z (wtOf Dw la 0), t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = δ + s.rho_vw ∧ t.hi = t.lo := by
  have hneg : wtOf Dw (-la) 0 + wtOf Dw la 0 = 0 := by rw [← wtOf_add', neg_add_cancel, wtOf_zero]
  have hi : ∀ σ, GoodEmb c σ → ∀ k, ((U σ).X k).IsSec (modelWt (U σ) (wtOf Dw (-la) 0) k) (rdU (U σ) s.inv k) := by
    intro σ hσ k
    rw [modelWt_congr (U σ) hσ (hU σ hσ) hla, modelWt_wtZ]
    refine (hU σ hσ).2.2.2.2.1 a 0 ha _ ?_ k
    rw [← secZ_nat, ← AllWt.exZ_wtZ, ← hla]
    exact s.symm.sig_mem
  have hs : ∀ σ, GoodEmb c σ → ∀ k, ((U σ).X k).IsSec (modelWt (U σ) (wtOf Dw la 0) k) (rdU (U σ) s.sig k) := by
    intro σ hσ k
    have he : ((U σ).X k).IsSec 0 (rdU (U σ) (idem Z) k) := by
      have h1 := (hU σ hσ).2.2.2.2.1 0 0 ⟨fun _ => antitone_const, Even.zero⟩ (idem Z) (by
        rw [← secZ_nat]
        convert idem_mem_secZ Z using 2
        funext i; cases i <;> rfl) k
      convert h1 using 1
      funext τ j; simp [laU]
    refine isSec_inv _ ?_ he (hi σ hσ k) ?_ ?_ ?_ ?_
    · rw [← modelWt_add _ (even_wtOf _ _) (even_wtOf _ _), add_comm, hneg]
      funext τ j; simp [modelWt]
    · exact (congrFun (AllWt.rdU_mul (U σ) _ _) k).symm.trans (by rw [idem_mul_idem])
    · exact (congrFun (AllWt.rdU_mul (U σ) _ _) k).symm.trans (by rw [s.idem_sig])
    · exact (congrFun (AllWt.rdU_mul (U σ) _ _) k).symm.trans (by rw [s.idem_inv])
    · exact (congrFun (AllWt.rdU_mul (U σ) _ _) k).symm.trans (by rw [s.mul_inv])
  have hb : ∀ {la δ} (s : ConstSec U x Z la δ) σ, GoodEmb c σ →
      ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw la 0) s.sig z ≤ C := fun s σ hσ => by
    have h := fun z hz => (s.homN_eq (σ := σ) (z := z) hz).le
    rw [show goodOf c σ = σ from if_pos hσ] at h
    exact ⟨_, h⟩
  refine ⟨TwSec.ofConst s hδ (fun G hG f hf => mul_mem_cuspOn_of_isSec (even_wtOf _ _) s.sig_mem s.sig_mem_suppOn hs
    (hb s) hG hf) (fun G hG f hf => ?_), rfl, rfl, rfl, rfl⟩
  have := mul_mem_cuspOn_of_isSec (even_wtOf (-la) 0) s.symm.sig_mem s.symm.sig_mem_suppOn hi (hb s.symm)
    (hG.add (even_wtOf la 0)) hf
  rwa [add_assoc, add_comm (wtOf Dw la 0), hneg, add_zero] at this

open Classical in

theorem exists_twSec_flat (hq : Dw.q = 0) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {Z : Comp Xo c} {τ : Psi H}
    (s : FlatSec U x Z τ) :
    ∃ t : TwSec U x Z (wtOf Dw (flatWt Dw τ) 0), t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = s.rho_vw ∧ t.hi = t.lo ∧
      t.degLo = s.deg := by
  obtain ⟨t, h1, h2, h3, h4⟩ := exists_twSec_of_dom hU s (finite_flDefect_vw τ)
    (a := fun y => if y.1 = τ.1 then 1 else 0) ⟨fun _ _ _ _ => le_rfl, Even.zero⟩ (by
      funext i
      rcases i with _ | ⟨ρ, i⟩
      · rfl
      · have hi := i.2
        have hρ : ρ (H.rt : E) = H.rt0 := by
          by_contra hn
          simp [Datum.mult, hn, hq] at hi
        refine (wtOf_big (-flatWt Dw τ) 0 ⟨ρ, hρ⟩ i (by simpa [Datum.mult, hρ] using hi)).trans ?_
        simp only [flatWt, parWt, sub_zero, Pi.neg_apply, exZ, wtZ]
        by_cases h1 : ρ = τ.1
        · rw [if_pos h1, if_pos (Subtype.ext h1)]; rfl
        · rw [if_neg h1, if_neg fun h2 => h1 (congrArg Subtype.val h2)]; rfl)
  have h0 : flDefect_vw Dw c τ = 0 := funext fun w => by simp [flDefect_vw, hq]
  replace h3 : t.lo = s.rho_vw := h3.trans ((congrArg (· + s.rho_vw) h0).trans (zero_add _))
  exact ⟨t, h1, h2, h3, h4, by rw [TwSec.degLo, h2, h3]; rfl⟩




end GlobalTheory.FlatTw
