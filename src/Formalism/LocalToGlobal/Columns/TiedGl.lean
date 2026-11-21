import Formalism.LocalToGlobal.Columns.TiedGlPl
import Formalism.LocalToGlobal.Columns.TiedGlMat
import Formalism.LocalToGlobal.Columns.RecLevelDiv
import Formalism.LocalToGlobal.HermitianForms.FormsTied

section
open Matrix NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions (Ranks)
open Formalism.L2.Forms (InJ aOf skipOf fcOf)

theorem gll_N (R : Ranks) (j : ℕ) : R.N j = R.k + j + j * R.t := by unfold Ranks.N; ring

theorem gll_t_pos (R : Ranks) : 0 < R.t := by have := R.rank_add_five_le; omega

theorem gll_Nm (R : Ranks) : R.N R.m = R.r + R.m * R.t + 1 := by
  rw [gll_N]; unfold Ranks.r; have := R.two_le_m; omega

section Steps

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {k' : Type} [Field k']

theorem colLevS_mem_iff {j : ℕ} (hj : j ≤ R.m) (w : Pr.vGs) (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* k')
    (M : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)) :
    M ∈ (colLevS Ch j w).H ↔
      InJ (aOf R j) R.t (fcOf R j) (decide (j = R.m)) ((M : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)).map e) := by
  rw [glm_InJ_map]
  have ht := gll_t_pos R
  by_cases h1 : j + 1 < R.m
  · have ha : aOf R j = R.k + j := if_pos (by omega)
    have hf : fcOf R j = R.N j := if_neg (by omega)
    have hd : decide (j = R.m) = false := decide_eq_false (by omega)
    rw [ha, hf, hd, glm_InJ_false (j := j) ht (by rw [gll_N]; omega), glm_fixCol_top le_rfl, inf_top_eq, colLevS_of_lt Ch h1]
    unfold colLev
    rw [if_pos (by omega)]
  · by_cases h2 : j + 1 = R.m
    · have ha : aOf R j = R.k + j := if_pos (by omega)
      have hf : fcOf R j = R.k := if_pos (by omega)
      have hd : decide (j = R.m) = false := decide_eq_false (by omega)
      rw [ha, hf, hd, glm_InJ_false (j := j) ht (by rw [gll_N]; omega)]
      unfold colLevS
      rw [if_neg h1, if_pos h2]
    · have hjm : j = R.m := by omega
      subst hjm
      have ha : aOf R R.m = R.r := if_neg (by omega)
      have hf : fcOf R R.m = R.k := if_pos (by omega)
      have hd : decide (R.m = R.m) = true := decide_eq_true rfl
      rw [ha, hf, hd, glm_InJ_true (j := R.m) ht (gll_Nm R), colLevS_top_H Ch le_rfl]
      rfl

theorem colLevS_lam_eq {j : ℕ} (hj : j ≤ R.m) (w : Pr.vGs) (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* k') (σ₀ : X.K →+* ℂ)
    (M : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)) (hM : M ∈ (colLevS Ch j w).H) :
    σ₀ (((colLevS Ch j w).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
      Formalism.L2.Forms.lamJ (glmPsi e σ₀ (Ch.psi0 w)) (fun s => glmChi e σ₀ (extChi (fun s => Ch.chi s w) s)) (aOf R j) R.t j (skipOf R j)
        ((M : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)).map e) := by
  have ht := gll_t_pos R
  have key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N j), l = colLevS Ch j w → ∀ hM' : M ∈ l.H,
      σ₀ ((l.lam ⟨M, hM'⟩ : X.Kˣ) : X.K) =
        Formalism.L2.Forms.lamJ (glmPsi e σ₀ (Ch.psi0 w)) (fun s => glmChi e σ₀ (extChi (fun s => Ch.chi s w) s)) (aOf R j) R.t j
          (skipOf R j) ((M : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)).map e) := by
    intro l hl hM'
    by_cases h1 : j + 1 < R.m
    · have ha : aOf R j = R.k + j := if_pos (by omega)
      have hs : skipOf R j = R.k := if_pos h1
      rw [ha, hs]
      have hl' : l = ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j,
          lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j⟩ := by
        rw [hl]; unfold colLevS colLev; rw [if_pos h1, if_pos (by omega)]
      subst hl'
      refine glm_lamGen e σ₀ _ _ (SX R.k R.m j) ht (by rw [gll_N]) (fun x hx => ?_) ⟨M, hM'⟩
      unfold SX
      rw [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨-, h | h⟩
        · exact h
        · omega
      · intro h; exact ⟨by omega, Or.inl h⟩
    · by_cases h2 : j + 1 = R.m
      · have ha : aOf R j = R.k + j := if_pos (by omega)
        have hs : skipOf R j = R.N j := if_neg h1
        rw [ha, hs]
        have hl' : l = ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j ⊓ fixCol (R.N j) (𝓞 X.E ⧸ w.1.asIdeal) R.k,
            (lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j).comp (Subgroup.inclusion inf_le_left)⟩ := by
          rw [hl]; unfold colLevS; rw [if_neg h1, if_pos h2]
        subst hl'
        refine glm_lamGen e σ₀ _ _ (SX R.k R.m j) ht (by rw [gll_N]) (fun x hx => ?_) ⟨M, hM'.1⟩
        unfold SX
        rw [Finset.mem_filter, Finset.mem_range]
        constructor
        · intro _; rw [gll_N]; omega
        · intro _; exact ⟨by omega, Or.inr h2⟩
      · have hjm : j = R.m := by omega
        subst hjm
        have ha : aOf R R.m = R.r := if_neg (by omega)
        have hs : skipOf R R.m = R.N R.m := if_neg h1
        rw [ha, hs]
        have hl' : l = ⟨HXmsharp (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m) R.k R.r R.t R.m,
            lamXmsharp (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N R.m) R.k R.r R.t R.m⟩ := by
          rw [hl]; unfold colLevS; rw [if_neg h1, if_neg h2]
        subst hl'
        refine glm_lamGen e σ₀ _ _ (Finset.range (R.r - 1)) ht (by rw [gll_Nm]; omega) (fun x hx => ?_) ⟨M, hM'.1.1⟩
        rw [Finset.mem_range]
        constructor
        · intro _; rw [gll_Nm]; omega
        · intro _; omega
  exact key _ rfl hM

theorem rowTyG_sharp_mem_iff (w : Pr.vGs) (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* k')
    (M : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) :
    M ∈ (rowTyG Ch (rPsharp Ch) w).H ↔
      InJ R.r R.t (fcOf R R.m) false ((M : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)).map e) := by
  have hf : fcOf R R.m = R.k := if_pos (by omega)
  rw [glm_InJ_map, hf, glm_InJ_false (j := R.m) (gll_t_pos R) (by rw [gll_Nm]; omega), rowTyG_sharp_H]
  rfl

theorem rowTyG_sharp_lam_eq (w : Pr.vGs) (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* k') (σ₀ : X.K →+* ℂ)
    (M : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hM : M ∈ (rowTyG Ch (rPsharp Ch) w).H) :
    σ₀ (((rowTyG Ch (rPsharp Ch) w).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
      Formalism.L2.Forms.lamJ (glmPsi e σ₀ (Ch.psi0 w)) (fun s => glmChi e σ₀ (extChi (fun s => Ch.chi s w) s)) R.r R.t R.m (R.N R.m)
        ((M : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)).map e) := by
  have h2 : M ∈ HJsharp (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m := (rowTyG_sharp_H Ch w) ▸ hM
  have h0 : M ∈ (rowTyG Ch (rP0 Ch) w).H := by rw [rowLevel_unipotent_group]; exact h2.1
  have e1 : (rowTyG Ch (rPsharp Ch) w).lam ⟨M, hM⟩ = (rowTyG Ch (rP0 Ch) w).lam ⟨M, h0⟩ := rfl
  rw [e1, rowLevel_unipotent_character Ch w M h0 h2.1]
  refine glm_lamGen e σ₀ _ _ (Finset.range (R.r - 1)) (gll_t_pos R) (by rw [gll_Nm]; omega) (fun x hx => ?_) ⟨M, h2.1⟩
  rw [Finset.mem_range]
  constructor
  · intro _; rw [gll_Nm]; omega
  · intro _; omega

end Steps

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM InJ)

section Prod

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)

include hc hPr in
theorem glk_under_mem (i : Fin 2) {w : Pl X.E} (hw : w ∈ Pr.vG i) : (Pr.g i : 𝓞 X.F) ∈ (underPl X.F w).asIdeal :=
  (glk_under hc hPr i _).1 ⟨w, hw, rfl⟩

theorem glk_gwOf_under (i : Fin 2) {w : Pl X.E} (hw : w ∈ Pr.vG i) :
    gwOf hc hPr i (underPl X.F w) (glk_under_mem hc hPr i hw) = ⟨w, glk_vG_le i hw⟩ :=
  (gwOf_uniq hc hPr i (underPl X.F w) (glk_under_mem hc hPr i hw) ⟨w, glk_vG_le i hw⟩
    (show (underPl X.F w).asIdeal = _ from rfl)).symm

open Classical in
theorem glk_prod_i (A : Pr.vGs → ℂ) (i : Fin 2) :
    ∏ w ∈ Pr.vG i, (if h : w ∈ Pr.vGs then A ⟨w, h⟩ else 1) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal), A (gwOf hc hPr i v h) := by
  have h1 : ∀ v : HeightOneSpectrum (𝓞 X.F), (∏ᶠ (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal), A (gwOf hc hPr i v h)) =
      if h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal then A (gwOf hc hPr i v h) else 1 := fun v => finprod_eq_dif _
  rw [finprod_congr h1]
  rw [finprod_eq_prod_of_mulSupport_subset (s := (Pr.vG i).image (underPl X.F))]
  · rw [Finset.prod_image]
    · refine Finset.prod_congr rfl fun w hw => ?_
      rw [dif_pos (glk_vG_le i hw), dif_pos (glk_under_mem hc hPr i hw), glk_gwOf_under hc hPr i hw]
    · intro w hw w' hw' e
      have e1 := glk_gwOf_under hc hPr i hw
      have e2 := glk_gwOf_under hc hPr i hw'
      have e3 : gwOf hc hPr i (underPl X.F w) (glk_under_mem hc hPr i hw) =
          gwOf hc hPr i (underPl X.F w') (glk_under_mem hc hPr i hw') := by
        congr 1
      rw [e1, e2] at e3
      exact congrArg Subtype.val e3
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    have hp : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := by
      by_contra hn
      exact hv (dif_neg hn)
    rw [Finset.coe_image]
    refine ⟨(gwOf hc hPr i v hp).1, gwOf_mem hc hPr i v hp, ?_⟩
    exact HeightOneSpectrum.ext (gwOf_over hc hPr i v hp).symm

theorem glk_prod (A : Pr.vGs → ℂ) :
    ∏ w : Pr.vGs, A w =
      ∏ i : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal), A (gwOf hc hPr i v h) := by
  classical
  have h0 : ∏ w : Pr.vGs, A w = ∏ w ∈ Pr.vGs, (if h : w ∈ Pr.vGs then A ⟨w, h⟩ else 1) := by
    rw [← Finset.prod_coe_sort Pr.vGs]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [dif_pos w.2]
  have hd : Disjoint (Pr.vG 0) (Pr.vG 1) := by
    rw [Finset.disjoint_left]
    intro w h0 h1
    exact hPr.g_ne ((hPr.vG_norm 0 w h0).symm.trans (hPr.vG_norm 1 w h1))
  rw [h0, Fin.prod_univ_two, ← glk_prod_i hc hPr A 0, ← glk_prod_i hc hPr A 1]
  unfold Primes.vGs
  convert Finset.prod_union hd using 2

end Prod

section GLc

variable {X : Fields} {Pr : Primes X} {hc : Formalism.BasicNotions.CMData X.F X.E} (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ)

def tieGLoc (hCh : Ch.Ok) : Formalism.L2.Forms.GLoc X.F X.E hc.sig Pr.g where
  sp := S.sp
  sp_sig := S.sp_sig
  sp_alg := S.sp_alg
  piG := Pr.piG
  piG_norm i := by
    have := congrArg (algebraMap (𝓞 X.E) X.E) (hPr.piG_norm i)
    rw [map_mul, map_natCast] at this
    exact this
  sp_pi := S.sp_pi
  psi0 i v h := glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h))
  psi_zero_nontrivial_character i v h := by
    intro h1
    apply hCh.psi_zero_nontrivial_character (gwOf hc hPr i v h)
    ext x
    have h2 := DFunLike.congr_fun h1 (S.eK hPr i v h x)
    rw [glmPsi_apply, AddChar.one_apply] at h2
    rw [AddChar.one_apply]
    exact σ₀.injective (h2.trans (map_one σ₀).symm)
  chiB i v h s := glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)

end GLc

end Formalism.L2.Col
end
end
