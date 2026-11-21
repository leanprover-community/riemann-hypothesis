import Formalism.LocalToGlobal.InertKernelTheory.ThetaSeriesDataHypothesesBelowMaximalLevel
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelCoupledLastLift
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelNonzeroUnit
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.LatticeShapeMiddleHolds
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FirstKernelSmallOfFrameTwist

section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelInstances

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}
variable {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} {u : D.what₂.Word} {μ : D.what₂.Tup}

theorem smul_one_tup (j : ℕ) (a : X.Lv.comp j) (L0 : (X.Pj j).Tup) : (X.Lv.lev j a).smul 1 L0 = L0 := by
  funext v
  ext z
  simp [Level.smul]

theorem clsBij_of (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ) (hjm : j ≤ X.mm)
    (hiff : ∀ (a a' : X.Lv.comp j) (L0 L1 : (X.Pj j).Tup), (X.Pj j).IsLatTup L0 → (X.Pj j).IsLatTup L1 →
      (cls j a L0 = cls j a' L1 ↔ a = a' ∧ ∃ γ : (X.Lv.lev j a).Γ, L1 = (X.Lv.lev j a).smul γ L0))
    (hsurj : ∀ x : (D.chTw u μ).cls j, ∃ a L0, (X.Pj j).IsLatTup L0 ∧ cls j a L0 = x) :
    ClsBij (Y := Y) u μ cls j := by
  constructor
  · rintro ⟨⟨a1, L1⟩, m1⟩ ⟨⟨a2, L2⟩, m2⟩ heq
    have hl1 := Y.Rep_lat j _ m1
    have hl2 := Y.Rep_lat j _ m2
    obtain ⟨rfl, γ, hγ⟩ := (hiff a1 a2 L1 L2 hl1 hl2).1 heq
    obtain ⟨L0, _, hu⟩ := Y.Rep_ex j hjm a1 L2 hl2
    have e1 : L1 = L0 := hu L1 ⟨m1, γ, hγ⟩
    have e2 : L2 = L0 := hu L2 ⟨m2, 1, (smul_one_tup j a1 L2).symm⟩
    subst e1
    subst e2
    rfl
  · intro x
    obtain ⟨a, L0, hL, hx⟩ := hsurj x
    obtain ⟨L1, ⟨hmem, γ, hγ⟩, _⟩ := Y.Rep_ex j hjm a L0 hL
    refine ⟨⟨(a, L1), hmem⟩, ?_⟩
    show cls j a L1 = x
    rw [← hx]
    exact (hiff a a L1 L0 (Y.Rep_lat j _ hmem) hL).2 ⟨rfl, γ, hγ⟩

theorem fq_le_span {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (j : ℕ)
    (hint : Submodule.span X.G.O (cmp j '' (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V)) = X.Lv.Int j) :
    X.FQ j ≤ Submodule.span X.G.Kf (Set.range (cmp j)) := by
  have h1 : X.Lv.Int j ≤ (Submodule.span X.G.Kf (Set.range (cmp j))).restrictScalars X.G.O := by
    rw [← hint]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, _, rfl⟩
    exact Submodule.subset_span ⟨x, rfl⟩
  exact Submodule.span_le.2 fun z hz => h1 hz

theorem cmp_mem_fq {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (j : ℕ)
    (hint : Submodule.span X.G.O (cmp j '' (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V)) = X.Lv.Int j)
    (y : ((ex.tw.fm u μ).lat j).V) : cmp j y ∈ X.FQ j := by
  have hy : y ∈ Submodule.span D.what₂.LL (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V) := by
    rw [((ex.tw.fm u μ).lat_good j).2.2]
    exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem z hz =>
    refine Submodule.subset_span ?_
    change cmp j z ∈ X.Lv.Int j
    rw [← hint]
    exact Submodule.subset_span (Set.mem_image_of_mem _ hz)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hb

theorem admissible_third_chain {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (j : ℕ)
    (hint : Submodule.span X.G.O (cmp j '' (((ex.tw.fm u μ).lat j).L : Set ((ex.tw.fm u μ).lat j).V)) = X.Lv.Int j)
    (hint' : Submodule.span X.G.O (cmp (j + 1) '' (((ex.tw.fm u μ).lat (j + 1)).L : Set ((ex.tw.fm u μ).lat (j + 1)).V)) =
      X.Lv.Int (j + 1))
    (hrat : (ex.tw.fm u μ).KRat j)
    (hCh : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) → X.Kz j (cmp j x) = cmp (j + 1) y)
    (F : X.Fm j) (hF : F ∈ X.FQ j) : X.Kz j F ∈ X.FQ (j + 1) := by
  have hs := fq_le_span cmp j hint hF
  clear hF
  induction hs using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, hy⟩ := hrat x
    rw [hCh x y hy]
    exact cmp_mem_fq cmp (j + 1) hint' y
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb => rw [map_smul]; exact Submodule.smul_mem _ a hb

theorem second_kernel_at_place (t : KerEntTied ex) {σ : D.what₂.LL →+* X.G.Kf} (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j)
    (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (hj : j < D.R.m)
    (hspan : X.FQ j ≤ Submodule.span X.G.Kf (Set.range (cmp j))) (hrat : (ex.tw.fm u μ).KRat j)
    (hCh : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) → X.Kz j (cmp j x) = cmp (j + 1) y)
    (hbij : ClsBij (Y := Y) u μ cls j) (hT : TiesAt t u μ cls cmp ι Rd Sr j) : SecondKernelAtLevel X Y j := by
  obtain ⟨hSh, hSt, hRd, hSer, cK, h1, h2, h3, hDel⟩ := hT
  refine ⟨cK, h1, h2, h3, ?_⟩
  intro F hF
  refine body_of_span Y j cK (Set.range (cmp j)) ?_ F (hspan hF)
  rintro _ ⟨x, rfl⟩ c' L' hL
  obtain ⟨y, hy⟩ := hrat x
  have hsum : (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) =
      ∑ c : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j c) : ℕ) : ℂ))⁻¹ • entRec t ex.tw u μ j c x := by
    have hQ := sharpQ_qOf (hSh x)
    funext c1 y1
    rw [compatible_lift_exists D L hT Gi Gl Kc0 Dx cX ex t u μ j hj _ _ hQ.1 hQ.2 c1 y1]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, entRec]
  rw [hCh x y hy, hRd y c' L' hL, hy, hsum, map_sum]
  rw [← Finset.sum_coe_sort (Y.Rep j)]
  symm
  refine Fintype.sum_bijective _ hbij _ _ fun La => ?_
  rw [map_smulₛₗ, map_inv₀, map_natCast, hSt La.1 La.2, hDel La.1 La.2 x c' L' hL,
    kernel_of_smul p X Y j La.1 (c', L') _ (hSer La.1 La.2 c' L' hL), mul_smul]

end Gen

theorem class_bijection_instance : ClsBijInst := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y j hj
  exact clsBij_of (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cls j (hj.trans_eq KA.fl_m.symm)
    (fun a a' L0 L1 h0 h1 => KA.cls_iff j hj a a' L0 L1 h0 h1) (KA.cls_surj j hj)

theorem admissible_third_instance : Adm3bInst := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om j hj F hF
  have hjm : j < D.R.m := lt_of_lt_of_eq hj KA.fl_m
  exact admissible_third_chain (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cmp j (KA.cmp_int j hjm.le)
    (KA.cmp_int (j + 1) hjm) (KA.rat j hjm) (fun x y hy => (KA.cmp_K j hjm x y hy).symm) F hF

theorem second_kernel_chain_instance : SecondKernelSingleLevel := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr j hj hTs
  have hsp := fq_le_span (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cmp j (KA.cmp_int j hj.le)
  have hch : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) →
      (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Kz j (KA.cmp j x) = KA.cmp (j + 1) y :=
    fun x y hy => (KA.cmp_K j hj x y hy).symm
  have hb : ClsBij (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) (Y := Y) u μ KA.cls j :=
    class_bijection_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y j hj.le
  exact second_kernel_at_place (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) (Y := Y) (σ := ex.cmp.embW u w h) t KA.cls KA.cmp ι Rd Sr
    j hj hsp (KA.rat j hj) hch hb hTs

theorem second_kernel_entry_instance : SecondKernelEntrywise := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr hTs j hj
  exact second_kernel_chain_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr j
    (by omega) (hTs j hj)

end Formalism.L2.KerInert.SecondKernelInstances
end
end

section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelCoupled

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}
variable {p : ℕ} [Fact p.Prime] {X : Sys p} {Y : Pend X} {u : D.what₂.Word} {μ : D.what₂.Tup}

theorem bodyC_of_span (Y : Pend X) (j : ℕ) (cK : Y.Kc) {I : Type} [Fintype I] (wt : I → Y.Kc) (La : I → X.Lt j)
    (S : Set (X.Fm j))
    (hS : ∀ F ∈ S, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ x : I, (wt x * cK) • Y.ker j (La x) (c', L') (F (La x).1 (La x).2))
    (F : X.Fm j) (hF : F ∈ Submodule.span X.G.Kf S) :
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ x : I, (wt x * cK) • Y.ker j (La x) (c', L') (F (La x).1 (La x).2) := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    intro c' L' _
    simp only [map_zero, Pi.zero_apply, ker_zero, smul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    intro c' L' hL
    simp only [map_add, Pi.add_apply, ker_add, smul_add, Finset.sum_add_distrib, hx c' L' hL, hy c' L' hL]
  | smul a x _ hx =>
    intro c' L' hL
    simp only [map_smul, Pi.smul_apply, ker_smul]
    rw [map_smul_Kf Y, hx c' L' hL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_comm]

theorem second_kernel_coupled (t : KerEntTied ex) {σ : D.what₂.LL →+* X.G.Kf} (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (ι : ℂ →+* Y.Kc)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (j : ℕ) (hj : j < D.R.m)
    (lp : (D.chTw u μ).cls j → X.Lt j)
    (hspan : X.FQ j ≤ Submodule.span X.G.Kf (Set.range (cmp j))) (hrat : (ex.tw.fm u μ).KRat j)
    (hCh : ∀ (x : ((ex.tw.fm u μ).lat j).V) (y : ((ex.tw.fm u μ).lat (j + 1)).V),
      (ex.tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) → X.Kz j (cmp j x) = cmp (j + 1) y)
    (hT : TiesC Y t u μ cmp ι Rd Sr j lp) (hH : HeckeC Y u μ j lp) : ExpansionDecomposition D X Y j := by
  obtain ⟨hSh, hRd, hLat, hDG, hSer, cK, h1, h2, _, hDel⟩ := hT
  have body := bodyC_of_span Y j cK (fun x : (D.chTw u μ).cls j => (((Nat.card ((D.chTw u μ).stab j x) : ℕ) : Y.Kc))⁻¹) lp
    (Set.range (cmp j)) (by
      rintro _ ⟨x, rfl⟩ c' L' hL
      obtain ⟨y, hy⟩ := hrat x
      have hsum : (D.chTw u μ).K j ((ex.tw.fm u μ).emb j x) =
          ∑ c : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j c) : ℕ) : ℂ))⁻¹ • entRec t ex.tw u μ j c x := by
        have hQ := sharpQ_qOf (hSh x)
        funext c1 y1
        rw [compatible_lift_exists D L hT Gi Gl Kc0 Dx cX ex t u μ j hj _ _ hQ.1 hQ.2 c1 y1]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, entRec]
      rw [hCh x y hy, hRd y c' L' hL, hy, hsum, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smulₛₗ, map_inv₀, map_natCast, hDel c x c' L' hL,
        kernel_of_smul p X Y j (lp c) (c', L') _ (hSer c c' L' hL), mul_smul])
  refine ⟨cK, h1, h2, (D.chTw u μ).cls j, Unit, inferInstance, inferInstance,
    fun x => Nat.card ((D.chTw u μ).stab j x), fun x _ => lp x, fun x _ => hLat x,
    fun x => ⟨Nat.card_pos, hDG x⟩, ?_, ?_⟩
  · intro F hF c' L' hL
    simpa only [Finset.univ_unique, Finset.sum_singleton] using body F (hspan hF) c' L' hL
  · intro v i F hF La' hLa'
    simpa only [Finset.univ_unique, Finset.sum_singleton] using hH v i F hF La' hLa'

end Gen

theorem second_kernel_coupled_instance : SecondKernelCoupledLastLift := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hm hTs hH
  have hj : D.R.m - 1 < D.R.m := by omega
  have hsp := fq_le_span (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) KA.cmp (D.R.m - 1) (KA.cmp_int (D.R.m - 1) hj.le)
  have hch : ∀ (x : ((ex.tw.fm u μ).lat (D.R.m - 1)).V) (y : ((ex.tw.fm u μ).lat (D.R.m - 1 + 1)).V),
      (ex.tw.fm u μ).emb (D.R.m - 1 + 1) y = (D.chTw u μ).K (D.R.m - 1) ((ex.tw.fm u μ).emb (D.R.m - 1) x) →
      (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Kz (D.R.m - 1) (KA.cmp (D.R.m - 1) x) = KA.cmp (D.R.m - 1 + 1) y :=
    fun x y hy => (KA.cmp_K (D.R.m - 1) hj x y hy).symm
  exact second_kernel_coupled (X := sysAt Ch std vp unif eO eO_spec dG dG_spec om) (Y := Y) (σ := ex.cmp.embW u w h) t KA.cmp ι Rd Sr
    (D.R.m - 1) hj lp hsp (KA.rat (D.R.m - 1) hj) hch hTs hH

theorem admissible_fourth_instance : Adm4NewInst := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hE hL
  have hmm : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm = D.R.m := KA.fl_m
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have hl : j + 1 < D.R.m := by omega
    obtain ⟨cK, h1, h2, _, hb⟩ :=
      second_kernel_entry_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr hE j hl
    exact ⟨cK, h1, h2, hb⟩
  · have hm : 0 < D.R.m := by omega
    obtain rfl : j = D.R.m - 1 := by omega
    obtain ⟨hT1, hH1⟩ := hL hm
    exact second_kernel_coupled_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp
      hm hT1 hH1

theorem hecke_coupled_entry : HeckeCEntry := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y lp hm h5b hsec hst
    v i F hF La' hLa'
  have hj : D.R.m - 1 < (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm :=
    lt_of_lt_of_eq (by omega : D.R.m - 1 < D.R.m) KA.fl_m.symm
  have hk := Pf.kadj_entry D h5b (Formalism.L2.G.Pend.up_down_adjoint D _ Y) (D.R.m - 1) hj v i F hF La' hLa'
  simp only [Finset.univ_unique, Finset.sum_singleton] at hk
  simp only [Pf.up_finsum]
  have hb : ClsBij (Y := Y) u μ KA.cls (D.R.m - 1) :=
    class_bijection_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y (D.R.m - 1)
      (by omega)
  have hbij : Function.Bijective fun x : (D.chTw u μ).cls (D.R.m - 1) =>
      (⟨lp x, (hsec x).1⟩ : {La // La ∈ Y.Rep (D.R.m - 1)}) := by
    constructor
    · intro x1 x2 he
      have h1 := (hsec x1).2
      have h2 := (hsec x2).2
      have : lp x1 = lp x2 := congrArg Subtype.val he
      rw [← h1, ← h2, this]
    · intro La
      refine ⟨KA.cls (D.R.m - 1) La.1.1 La.1.2, ?_⟩
      apply hb.1
      show KA.cls (D.R.m - 1) (lp _).1 (lp _).2 = KA.cls (D.R.m - 1) La.1.1 La.1.2
      exact (hsec _).2
  have hw : ∀ x : (D.chTw u μ).cls (D.R.m - 1),
      Nat.card ((D.chTw u μ).stab (D.R.m - 1) x) = (sysAt Ch std vp unif eO eO_spec dG dG_spec om).stab (D.R.m - 1) (lp x) := by
    intro x
    have e := hst (lp x) (hsec x).1
    rw [(hsec x).2] at e
    exact e
  refine (Fintype.sum_bijective _ hbij _ _ fun x => ?_).trans (hk.trans (Fintype.sum_bijective _ hbij _ _ fun x => ?_).symm)
  · simp only [hw x]
  · simp only [hw x]

theorem coupled_compatibility_at_place : TiesCOfAt := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y ι Rd Sr lp hm hsec hTs
  obtain ⟨hSh, hSt, hRd, hSer, cK, h1, h2, h3, hDel⟩ := hTs
  refine ⟨hSh, hRd, fun x => Y.Rep_lat _ _ (hsec x).1, fun x => ?_, fun x c' L' hL => hSer (lp x) (hsec x).1 c' L' hL,
    cK, h1, h2, h3, fun x y c' L' hL => ?_⟩
  · have e := hSt (lp x) (hsec x).1
    rw [(hsec x).2] at e
    rw [e]
    exact dG_spec (D.R.m - 1) (by have := KA.fl_m; omega) (lp x).1 (lp x).2 (Y.Rep_lat _ _ (hsec x).1)
  · have e := hDel (lp x) (hsec x).1 y c' L' hL
    rw [(hsec x).2] at e
    exact e

theorem coupled_section_exists : SecCEx := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y hm
  have hb : ClsBij (Y := Y) u μ KA.cls (D.R.m - 1) :=
    class_bijection_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om Y (D.R.m - 1)
      (by omega)
  refine ⟨fun x => (Function.surjInv hb.2 x).1, fun x => ⟨(Function.surjInv hb.2 x).2, ?_⟩⟩
  exact Function.surjInv_eq hb.2 x

end Formalism.L2.KerInert.SecondKernelCoupled
end
end

section
noncomputable section

namespace Formalism.L2.KerInert.AdmLoc2

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

section Law

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (be : MvPowerSeries (Fin 2) (Formalism.L2.G.Pend.K0 p))

theorem admissible_stabilizer_of_law (D : Formalism.BasicNotions.D7) (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) :
    StabLawLt X E hfin ThR → Formalism.MainNotions.FormalGroupSystem.MinkowskiCounting D X (pendR X E hfin hst be ThR) := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E
  intro hS
  classical
  let ThR' : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p] :=
    fun j La La' => if j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2 then ThR j La La' else 0
  have hS' : StabLaw X ℂ_[p] hfin ThR' := by
    intro j c L0 La' ε h0 hε
    by_cases hj : j < X.mm ∧ (X.Pj (j + 1)).IsLatTup La'.2
    · simp only [ThR', if_pos hj]
      exact hS j hj.1 c L0 La' ε h0 hj.2 hε
    · simp only [ThR', if_neg hj]
      unfold SA
      rw [← MvPowerSeries.coe_substAlgHom (hasSubst_actS X ℂ_[p] j _), map_zero, mul_zero]
  have hK := kapLaw_of_stabLaw X ℂ_[p] hfin ThR' pC_ne_zero hS'
  intro j hj c L La' γ G hGv hL hLa'
  have hEq : ∀ La, thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR') j La La' = thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j La La' := by
    intro La
    simp only [thFN, thGeo, ThR', if_pos (And.intro hj hLa')]
  have key : ∀ t : X.G.Kf,
      (eSX X j (c, (X.Lv.lev j c).smul γ L) * t) •
          delF X ℂ_[p] j ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G)
            (thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j (c, (X.Lv.lev j c).smul γ L) La') =
        (eSX X j (c, L) * t) • delF X ℂ_[p] j G (thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin ThR) j (c, L) La') := by
    intro t
    have := ker_law X ℂ_[p] pC_ne_zero (delEquivOn_GdC X ℂ_[p]) _ hK j c L La' γ G hL (vtIn_GdC X ℂ_[p] j G hGv) t
    rwa [hEq, hEq] at this
  exact key _

end Law

end Formalism.L2.KerInert.AdmLoc2

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.AdmLoc2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F
open Formalism.L2.KerInert.AdmLoc (pendG CurveIn XiIn)

theorem admissible_general_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmGen2 := by
  intro D p _ X _ E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw h3b h4
  obtain ⟨h5, hAt, hin, hW, hcc, hδ, hχ, hlam, hLam⟩ := hC
  obtain ⟨hA, hcl, hXa, hS, ρ, hLP, hMI, hFL⟩ := hK
  obtain ⟨h2, h2b, h3⟩ := hK1 D p h5 X E hfin hst g hLT pos fd cc δ B χ lam SS cl Ξ₀ muT ρ
    hAt hin hW hcc hδ hχ hlam hLam hA hcl hXa hS hLP hMI hFL
  refine ⟨Formalism.MainNotions.FormalGroupSystem.Pf.positivity_condition_holds D, h2, h2b, ?_, h3, h3b, h4, ?_, ?_, Formalism.L2.G.Pend.up_down_adjoint D X _,
    Formalism.L2.PairingIndexBounds.Ent.pending_tuple_admissible X E hfin hst hLT pos _ D, Formalism.L2.KerInert.admissible_all_levels D p X, ?_⟩
  · exact Formalism.L2.KerInert.admissible_second_inert D cc δ p g hLT hAt h5 hin hW X _ rfl
  · exact (invariance_iff_additive_maps_exist X E hfin hst hLT pos _ D).2 hXi
  · exact admissible_stabilizer_of_law X E.toCEmb hfin hst (beLT hLT) D _ hLaw
  · exact Formalism.L2.KerInert.admissible_eleventh_inert D cc δ p g hLT hAt h5 hin hW X _ rfl

section At

open Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelCoupled

theorem admissible_place_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmAt2 := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos
    Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies
  obtain ⟨ι, Rd, Sr, hE, hL⟩ := hTies
  have hmm : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).mm = D.R.m := KA.fl_m
  refine admissible_general_of_kernel_law hK1 D _ (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst g hLT pos _ cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw
    (admissible_third_instance D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om) ?_
  by_cases hm : 0 < D.R.m
  · obtain ⟨lp, hTC, hH⟩ := hL hm
    exact admissible_fourth_instance D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hE (fun _ => ⟨hTC, hH⟩)
  · exact ⟨fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩

theorem admissible_entries_of_kernel_law (hK1 : Formalism.L2.KerInert.KGLt.TranslatesOfInertKernelAtPlace) : AdmAtEnt2 := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ w h _ Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ E hfin hst g hLT pos
    Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT hC hK hXi hLaw hTies
  obtain ⟨ι, Rd, Sr, hA⟩ := hTies
  have h5b := admissible_stabilizer_of_law (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E.toCEmb hfin hst (beLT hLT) D _ hLaw
  refine admissible_place_of_kernel_law hK1 D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om E hfin hst g hLT pos Tw I L0 a bad cc δ B χ lam SS cl Ξ₀ muT
    hC hK hXi hLaw ⟨ι, Rd, Sr, fun j hj => hA j (by omega), fun hm => ?_⟩
  obtain ⟨lp, hsec⟩ := coupled_section_exists D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ hm
  have hT1 := hA (D.R.m - 1) (by omega)
  exact ⟨lp, coupled_compatibility_at_place D L hT Gi Gl Kc0 Dx cX ex t u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ ι Rd Sr lp hm hsec hT1,
    hecke_coupled_entry D L hT Gi Gl Kc0 Dx cX ex u μ w h Fl Lv Ch KA std vp unif eO eO_spec dG dG_spec om _ lp hm h5b hsec hT1.2.1⟩

end At

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem admissible_entries_small_chain : AdmAtEnt2 := admissible_entries_of_kernel_law Formalism.L2.KerInert.KGLt.first_kernel_law_global_small

end Formalism.L2.KerInert.AdmLoc2
end
end
