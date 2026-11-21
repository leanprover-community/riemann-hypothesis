import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocSupStep

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem tsum_mix {ι W : Type} (Wd : Finset W) (m : ι → ℝ) (hm0 : ∀ i, 0 ≤ m i) (hms : Summable m)
    (hM : 0 < ∑' i, m i) (q : ι → W → ℝ) (hq : ∀ i, TB.IsProb Wd (q i)) :
    ∃ θ : W → ℝ, TB.IsProb Wd θ ∧ ∀ N : W → ℝ,
      Summable (fun i => m i * ∑ u ∈ Wd, q i u * N u) ∧
      ∑' i, m i * ∑ u ∈ Wd, q i u * N u = (∑' i, m i) * ∑ u ∈ Wd, θ u * N u := by
  set M := ∑' i, m i with hMdef
  have hq1 : ∀ i u, q i u ≤ 1 := by
    intro i u
    by_cases hu : u ∈ Wd
    · rw [← (hq i).2.2]
      exact Finset.single_le_sum (fun a _ => (hq i).1 a) hu
    · rw [(hq i).2.1 u hu]
      exact zero_le_one
  have hsu : ∀ u, Summable (fun i => m i * q i u) := fun u =>
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hm0 i) ((hq i).1 u))
      (fun i => mul_le_of_le_one_right (hm0 i) (hq1 i u)) hms
  refine ⟨fun u => (∑' i, m i * q i u) / M, ⟨fun u => div_nonneg (tsum_nonneg fun i =>
    mul_nonneg (hm0 i) ((hq i).1 u)) hM.le, fun u hu => ?_, ?_⟩, fun N => ⟨?_, ?_⟩⟩
  · simp [(hq _).2.1 u hu]
  · rw [← Finset.sum_div, div_eq_one_iff_eq hM.ne', ← Summable.tsum_finsetSum (fun u _ => hsu u)]
    refine tsum_congr fun i => ?_
    rw [← Finset.mul_sum, (hq i).2.2, mul_one]
  · simp_rw [Finset.mul_sum, ← mul_assoc]
    exact summable_sum fun u _ => (hsu u).mul_right (N u)
  · simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Summable.tsum_finsetSum (fun u _ => (hsu u).mul_right (N u))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [tsum_mul_right]
    field_simp

theorem mL_pat {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) :
    crystallineComparison.mL K L σ * ∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K = ∏ v ∈ crystallineComparison.pat L σ, L v ^ K := by
  have h1 : ∀ v ∈ crystallineComparison.pat L σ, crystallineComparison.mfac K (L v) ‖σ v‖ * ‖σ v‖ ^ K = L v ^ K := by
    intro v hv
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have ha : 0 < ‖σ v‖ := lt_of_le_of_lt (hL v) hv
    have hle : (L v / ‖σ v‖) ^ K ≤ 1 :=
      pow_le_one₀ (div_nonneg (hL v) ha.le) ((div_le_one ha).mpr hv.le)
    unfold crystallineComparison.mfac
    rw [if_neg ha.ne', min_eq_right hle, div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ ha.ne'
  have h2 : ∀ v ∈ (Finset.univ : Finset (Fin f)), v ∉ crystallineComparison.pat L σ → crystallineComparison.mfac K (L v) ‖σ v‖ = 1 := by
    intro v _ hv
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
    unfold crystallineComparison.mfac
    split_ifs with h0
    · rfl
    · have ha : 0 < ‖σ v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      exact min_eq_left (one_le_pow₀ ((one_le_div ha).mpr hv))
  unfold crystallineComparison.mL
  rw [← Finset.prod_subset (Finset.subset_univ _) h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl h1

theorem bound_mL {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) (X Y : ℝ)
    (h : (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * X ≤ (∏ v ∈ crystallineComparison.pat L σ, L v ^ K) * Y) : X ≤ crystallineComparison.mL K L σ * Y := by
  have hP : 0 < ∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K := by
    refine Finset.prod_pos fun v hv => pow_pos ?_ _
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact lt_of_le_of_lt (hL v) hv
  rw [← mL_pat K L hL σ] at h
  refine le_of_mul_le_mul_left ?_ hP
  calc (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * X
      ≤ crystallineComparison.mL K L σ * (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * Y := h
    _ = (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * (crystallineComparison.mL K L σ * Y) := by ring

theorem mL_nonneg {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) : 0 ≤ crystallineComparison.mL K L σ := Finset.prod_nonneg fun v _ => by
    unfold crystallineComparison.mfac
    split_ifs
    · exact zero_le_one
    · exact le_min zero_le_one (pow_nonneg (div_nonneg (hL v) (norm_nonneg _)) _)

theorem mL_zero {f : ℕ} (K : ℕ) (L : Fin f → ℝ) : crystallineComparison.mL K L 0 = 1 := by
  unfold crystallineComparison.mL crystallineComparison.mfac
  simp

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem prod_gN (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i : ℕ) (w : S.W) (p q : Fin S.f → C.LPt) :
    ∏ v, KB.gN S v ε i (w.1 v) (p v) (q v) =
      (∏ v, S.gramLoc v ε i (w.1 v) (p v) (q v)) / (C.Word.size S.P w.1 : ℂ) := by
  unfold KB.gN C.Word.size
  rw [Finset.prod_div_distrib]
  congr 1
  push_cast
  rfl

theorem nstV_eq (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : Fin S.f → ℂ) :
    KB.NstV S ε i s w Y κ t t' = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' *
      ∏ v, KB.gN S v ε i (w.1 v) (C.loc (S.σ v) h ++ [(s, t v)]) (C.loc (S.σ v) h' ++ [(s, t' v)]) := by
  unfold KB.NstV
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h' _ => ?_
  have e := prod_gN S ε i w (fun v => C.loc (S.σ v) h ++ [(s, t v)]) (fun v => C.loc (S.σ v) h' ++ [(s, t' v)])
  rw [e, mul_div_assoc]

end setting

end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def GSup (S : C.HidaSetting E Wp Wq) (ε : ℝ) (b n : ℕ) (P : ℝ) : Prop :=
  ∀ w' ∈ S.base.Wall, S.base.cnt w' + n * C.Kst ≤ S.Ntop →
    ∃ θ : S.W → ℝ, TB.IsProb (S.base.Wb (S.base.cnt w' + n * C.Kst)) θ ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = b - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ t : crystallineComparison.V S.f, Good t →
          (KB.NstV S ε (b + n - 1) n w' Y κ t t).re ≤
            P * ∑ u ∈ S.base.Wb (S.base.cnt w' + n * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ

theorem integrable_inv_cube : Integrable (fun c : ℂ => ((1 + ‖c‖) ^ 3)⁻¹) := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  show (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹
  rw [Real.rpow_neg (by positivity)]
  norm_cast

theorem zero_mem_dual {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) : (0 : crystallineComparison.V f) ∈ crystallineComparison.dualSet La := by
  intro z _; simp [Lat.psi_zero]

theorem one_le_tsum_mL {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (g : ℝ)
    (hs : Summable fun σ : crystallineComparison.dualSet La => crystallineComparison.mL K L (g • (σ : crystallineComparison.V f))) :
    1 ≤ ∑' σ : crystallineComparison.dualSet La, crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) := by
  have := hs.le_tsum (⟨0, zero_mem_dual La⟩ : crystallineComparison.dualSet La) (fun σ _ => mL_nonneg K L hL _)
  simpa [mL_zero] using this

theorem gN_one_reg (S : C.HidaSetting E Wp Wq) (hI : KB.IntAll S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (b : ℕ)
    (hb : 1 ≤ b) (hbr : b ≤ S.G.r + 1) (w : S.W) (h h' : C.LPt) (hh : D.ptSize h = b - 1)
    (hh' : D.ptSize h' = b - 1) :
    ContinuousOn (fun c => KB.gN S v ε (b + 1 - 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) {0}ᶜ ∧
    Integrable (fun c => KB.gN S v ε (b + 1 - 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) := by
  obtain ⟨φ, hφc, hφ, ⟨Cφ, hC⟩, -⟩ := hI v ε hε b hb hbr w h h' hh hh'
  have e : b + 1 - 1 = b := by omega
  rw [e]
  have hcongr : ∀ c ∈ ({0}ᶜ : Set ℂ), φ c / (S.sizeAt v (w.1 v) : ℂ) =
      KB.gN S v ε b (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) := by
    intro c hc
    unfold KB.gN
    rw [hφ c hc]
  have hφi : Integrable φ :=
    Integrable.mono' (integrable_inv_cube.const_mul Cφ) hφc.aestronglyMeasurable (ae_of_all _ hC)
  refine ⟨(hφc.div_const _).continuousOn.congr fun c hc => (hcongr c hc).symm, ?_⟩
  refine (hφi.div_const (S.sizeAt v (w.1 v) : ℂ)).congr ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with c hc
  exact hcongr c hc

def SumBound (f : ℕ) (Cs : ℝ) : Prop :=
  ∀ (R g : ℝ) (L : Fin f → ℝ), 0 < R → 0 < g → (∀ v, 0 ≤ L v) →
    Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f))) ∧
    ∑' σ : crystallineComparison.dualSet (Lstd f R), crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f)) ≤ ∏ v, Cs * (1 + (R * L v / g) ^ 2)

theorem size_step (f : ℕ) (Cs : ℝ) (hCs1 : 1 ≤ Cs) (dl R g : ℝ) (hdl : 0 ≤ dl) (hR : 0 < R) (hg : 0 < g)
    (L thr : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v ∧ L v ≤ thr v) (M V : ℝ) (hM : M ≤ ∏ v, Cs * (1 + (R * L v / g) ^ 2))
    (hV : dl * (∏ v, Cs * (1 + (R * thr v / g) ^ 2)) / R ^ (2 * f) ≤ V) : dl * M / R ^ (2 * f) ≤ V := by
  refine le_trans ?_ hV
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left (hM.trans ?_) hdl
  refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  have h1 : R * L v / g ≤ R * thr v / g := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hL v).2 hR.le) hg.le
  have h0 : 0 ≤ R * L v / g := div_nonneg (mul_nonneg hR.le (hL v).1) hg.le
  nlinarith

theorem gsup_one (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hpos : C.ThmPPos S) (hI : KB.IntAll S)
    (X : ℕ → Fin S.f → ℝ) (hW : ∀ v, KB.WaveLoc S v fun i => X i v) (ε : ℝ) (hε : 0 < ε) (b : ℕ) (hb : 1 ≤ b)
    (hbr : b ≤ S.G.r + 1) (hX : ∀ v, 0 ≤ X b v ∧ X b v ≤ thr S b 1 v) (Cs : ℝ) (hCs1 : 1 ≤ Cs)
    (hCs : SumBound S.f Cs) (B R : ℝ) (hR : 0 < R)
    (hRB : (∏ _v : Fin S.f, KB.dlB S b 1) * (∏ v, Cs * (1 + (R * thr S b 1 v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
      B ^ S.f * S.base.vol b 1) :
    ∃ P, 0 ≤ P ∧ P ≤ B ^ S.f * S.base.vol b 1 ∧ GSup S ε b 1 P := by
  obtain ⟨i1, i2, hcov, -⟩ := pbc_lstdFacts S.f R hR
  have := i1; have := i2
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  have hL0 : ∀ v, 0 ≤ X b v := fun v => (hX v).1
  obtain ⟨hsm, hsle⟩ := hCs R S.g (fun v => X b v) hR hg' hL0
  have hM1 := one_le_tsum_mL (Lstd S.f R) C.Kst (fun v => X b v) hL0 (S.g : ℝ) hsm
  set M := ∑' σ : crystallineComparison.dualSet (Lstd S.f R), crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) with hMdef
  have hdl0 : 0 ≤ ∏ _v : Fin S.f, KB.dlB S b 1 := Finset.prod_nonneg fun v _ => (dlB_pos S hg b 1).le
  refine ⟨(∏ _v : Fin S.f, KB.dlB S b 1) * M / R ^ (2 * S.f), by positivity,
    size_step S.f Cs hCs1 _ R S.g hdl0 hR hg' _ (thr S b 1) hX M _ hsle hRB, ?_⟩
  intro w' hw' hcnt
  simp only [one_mul] at hcnt ⊢
  obtain ⟨θ, hθ, hWV⟩ := Formalism.FourierDecayAlt.P.plane_wave_bound E Wp Wq S X hW ε hε b hb hbr w' hw' hcnt
  obtain ⟨θ', hθ', hmix⟩ := tsum_mix (S.base.Wb (S.base.cnt w' + C.Kst))
    (fun σ : crystallineComparison.dualSet (Lstd S.f R) => crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))
    (fun σ => mL_nonneg _ _ hL0 _) hsm (by linarith)
    (fun σ => θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))) (fun σ => hθ _)
  refine ⟨θ', hθ', fun Y hY κ hκ t ht => ?_⟩
  let D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ := fun v h h' c =>
    KB.gN S v ε (b + 1 - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(1, c)]) (C.loc (S.σ v) h' ++ [(1, c)])
  have hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z) := by
    intro v z _
    have := PBB.gN_psd S hpos v ε hε (b + 1 - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(1, z)])
    exact JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(1, z)])
      (fun h hh => Finset.mem_image_of_mem _ hh)
  have hreg := fun v h (hh : h ∈ Y) h' (hh' : h' ∈ Y) =>
    gN_one_reg S hI v ε hε b hb hbr w' (C.loc (S.σ v) h) (C.loc (S.σ v) h')
      (by rw [JCx1.needs.ptSize_loc]; exact hY h hh) (by rw [JCx1.needs.ptSize_loc]; exact hY h' hh')
  set N0 : S.W → ℝ := fun u => S.base.N0 ε (b - 1) u Y κ
  have hF : ∀ σ ∈ crystallineComparison.dualSet (Lstd S.f R),
      ‖Hh Y κ (fun v l h h' => KB.hatB S v ε b 1 (w'.1 v) l (C.loc (S.σ v) h) (C.loc (S.σ v) h'))
        ((S.g : ℝ) • σ)‖ ≤ crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • σ) *
          ∑ u ∈ S.base.Wb (S.base.cnt w' + C.Kst), θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • σ)) u * N0 u := by
    intro σ _
    exact bound_mL C.Kst (fun v => X b v) hL0 _ _ _ (hWV Y hY κ hκ _ _)
  have hH := herglotz_plain (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1)
    (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b 1)
    (fun _ => dlB_pos S hg b 1)
    (fun v l h h' => KB.hatB S v ε b 1 (w'.1 v) l (C.loc (S.σ v) h) (C.loc (S.σ v) h')) (fun _ _ _ _ => rfl)
    (Lstd S.f R)
    (fun σ : crystallineComparison.V S.f => crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • σ) *
      ∑ u ∈ S.base.Wb (S.base.cnt w' + C.Kst), θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • σ)) u * N0 u)
    (hmix N0).1 (fun σ hσ => hF σ hσ)
    t {t} (by simp)
  rw [(hmix N0).2, hcov, Finset.sum_singleton] at hH
  have hN : Nz Y κ D t = (KB.NstV S ε (b + 1 - 1) 1 w' Y κ t t).re := by
    simp only [Nz, if_pos ht]
    rw [nstV_eq]
    rfl
  rw [hN] at hH
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
  linarith [hH]

end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem mem_Wb_iff (S : C.HidaSetting E Wp Wq) (m : ℕ) (u : S.W) : u ∈ S.base.Wb m ↔ u ∈ S.base.Wall ∧ S.base.cnt u ≤ m :=
  Finset.mem_filter

theorem Wb_mono (S : C.HidaSetting E Wp Wq) {m m' : ℕ} (h : m ≤ m') : S.base.Wb m ⊆ S.base.Wb m' := by
  intro u hu
  rw [mem_Wb_iff] at hu ⊢
  exact ⟨hu.1, hu.2.trans h⟩

theorem prob_sum_sub {W : Type} {A Wd : Finset W} {θ : W → ℝ} (hθ : TB.IsProb A θ) (h : A ⊆ Wd) :
    ∑ u ∈ Wd, θ u = 1 := by
  rw [← hθ.2.2]
  exact (Finset.sum_subset h fun u _ hu => hθ.2.1 u hu).symm

theorem blockPSD_same {α : Type} (Y : Finset α) (κ : α → α → ℂ) (hκ : TB.PSDOn Y κ) : KB.BlockPSD Y Y κ κ κ := by
  rw [blockPSD_iff]
  have := JCx1.decay.psd_pull Y κ hκ (Y.disjSum Y) (Sum.elim id id) (by
    intro x hx
    rcases x with p | p
    · rw [Finset.inl_mem_disjSum] at hx; exact hx
    · rw [Finset.inr_mem_disjSum] at hx; exact hx)
  refine PBB.psd_congr _ _ _ (fun x hx y hy => ?_) this
  rcases x with p | p <;> rcases y with q | q
  · rfl
  · rfl
  · rw [Finset.inr_mem_disjSum] at hx
    rw [Finset.inl_mem_disjSum] at hy
    simp only [blk, Sum.elim_inl, Sum.elim_inr, id]
    exact psd_herm Y κ hκ hy hx
  · rfl

theorem image_prod_loc {X : Type} (σ : E →+* ℂ) (Y : Finset (TB.Pt E)) (Xs : Finset X) :
    (Y ×ˢ Xs).image (fun p : TB.Pt E × X => (C.loc σ p.1, p.2)) = (Y.image (C.loc σ)) ×ˢ Xs := by
  ext ⟨a, x⟩
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨h, x', ⟨hh, hx'⟩, rfl, rfl⟩; exact ⟨⟨h, hh, rfl⟩, hx'⟩
  · rintro ⟨⟨h, hh, rfl⟩, hx⟩; exact ⟨h, x, ⟨hh, hx⟩, rfl, rfl⟩

theorem germ_global (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (w' : S.W)
    (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop) (Y : Finset (TB.Pt E)) (hY : ∀ h ∈ Y, TB.level h = b - 1) :
    ∃ (P Q : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ),
      (∀ v, ∀ h ∈ Y, ∀ h' ∈ Y,
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)]))) ∧
      GermData Y (fun v p q => KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)])
          (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])) P Q
        (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) := by
  have hloc : ∀ v, ∀ h ∈ Y.image (C.loc (S.σ v)), D.ptSize h = b - 1 := by
    intro v h hh
    obtain ⟨h0, hh0, rfl⟩ := Finset.mem_image.1 hh
    rw [JCx1.needs.ptSize_loc]; exact hY h0 hh0
  have hsup : ∀ v, ∃ B : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ t : ℂ, t ≠ 0 →
      ‖KB.gN S v ε (b + n - 2) (w'.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t)])‖ ≤ B := by
    intro v
    have hs : ∀ h ∈ Y.image (C.loc (S.σ v)), LocSup S v ε (n - 1) b (w'.1 v) h := by
      intro h hh
      refine locSup_all S hpos hI hg v Λ (hLL v) (hGL v) (fun b s hb hs hbs => hΛ0 b s hb hs hbs v) ε hε (n - 1)
        (by omega) b hb (by omega) h (hloc v h hh) (w'.1 v) ⟨w', rfl⟩ ?_
      have := PBB.len_le_cnt S w' v
      have hk : (n - 1 - 1) * C.Kst ≤ n * C.Kst := Nat.mul_le_mul_right _ (by omega)
      omega
    choose! Bh hBh using hs
    refine ⟨∑ h ∈ Y.image (C.loc (S.σ v)), max (Bh h) 0, fun h hh t ht => ?_⟩
    have := hBh h hh t ht
    rw [show b + (n - 1) - 1 = b + n - 2 by omega] at this
    exact this.trans ((le_max_left _ _).trans (Finset.single_le_sum (f := fun h => max (Bh h) 0)
      (fun _ _ => le_max_right _ _) hh))
  have hG' : ∀ v, ∃ (Pu Pa : C.LPt × ℂ → C.LPt × ℂ → ℂ),
      (∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)),
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)]))) ∧
      (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (fun p q => KB.gN S v ε (b + n - 2) (w'.1 v) (p.1 ++ [(n - 1, p.2⁻¹)]) (q.1 ++ [(n - 1, q.2⁻¹)])) Pu Pa) ∧
      (∃ B' : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ x : ℂ, x ≠ 0 → ‖Pa (h, x) (h, x)‖ ≤ B') ∧
      ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)), ∀ σ : ℂ,
        Tendsto (fun x => Pa (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => Pu (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => conj (Pu (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) := by
    intro v
    obtain ⟨h1, Pu, Pa, h2, h3, h4⟩ := hGL v ε hε b n hb hn hbn (w'.1 v) ⟨w', rfl⟩ (Y.image (C.loc (S.σ v)))
      (hloc v) (hsup v)
    exact ⟨Pu, Pa, h1, h2, h3, h4⟩
  choose Pu Pa hcont hblk hB' hlim using hG'
  choose Bs hBs using hsup
  choose B' hB'' using hB'
  have mem : ∀ v, ∀ h ∈ Y, C.loc (S.σ v) h ∈ Y.image (C.loc (S.σ v)) := fun v h hh => Finset.mem_image_of_mem _ hh
  refine ⟨fun v p q => Pu v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v p q => Pa v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v h hh h' hh' => hcont v _ (mem v h hh) _ (mem v h' hh'), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro v Xs hXs
    have := hblk v Xs hXs
    rw [← image_prod_loc (S.σ v) Y Xs] at this
    exact PBB.blockPSD_pull (Y ×ˢ Xs) (fun p : TB.Pt E × ℂ => (C.loc (S.σ v) p.1, p.2)) _ _ _ this
  · refine ⟨∑ v, (max (Bs v) 0 + max (B' v) 0), Finset.sum_nonneg fun v _ => by positivity,
      fun v h hh x hx => ⟨?_, ?_⟩⟩
    · refine ((hBs v _ (mem v h hh) x⁻¹ (inv_ne_zero hx)).trans (le_max_left (Bs v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_right (le_max_right (B' v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
    · refine ((hB'' v _ (mem v h hh) x hx).trans (le_max_left (B' v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_left (le_max_right (Bs v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.2

end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem germ_step (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (P' : ℝ) (hP' : GSup S ε b (n - 1) P')
    (hP'0 : 0 ≤ P') (w' : S.W) (hw' : w' ∈ S.base.Wall) (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop)
    (La : Submodule ℤ (crystallineComparison.V S.f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (hsm : Summable fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) :
    ∃ θ : S.W → ℝ, TB.IsProb (S.base.Wb (S.base.cnt w' + n * C.Kst)) θ ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = b - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ (z₀ : crystallineComparison.V S.f) (Ss : Finset (crystallineComparison.V S.f)), (∀ z ∈ Ss, z - z₀ ∈ La) → (∀ z ∈ Ss, Good z) →
          ZLattice.covolume La * ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re ≤
            (∏ _v : Fin S.f, KB.dlB S b n) *
              ((∑' σ : crystallineComparison.dualSet La, crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) * P') *
              ∑ u ∈ S.base.Wb (S.base.cnt w' + n * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ := by
  have hk : n * C.Kst = (n - 1) * C.Kst + C.Kst := by
    have : n = (n - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [add_mul, one_mul]
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  set L : Fin S.f → ℝ := fun v => Λ b (n - 1) v with hLdef
  have hL0 : ∀ v, 0 ≤ L v := fun v => hΛ0 b (n - 1) hb (by omega) (by omega) v

  obtain ⟨θL, hθL, hLV⟩ := Formalism.FourierDecayAlt.P.lift_bound_below_top_all_places E Wp Wq S Λ hpos hLL ε hε (b + n - 2) (n - 1) (by omega)
    (by omega) (by omega) w' hw' (by omega)
  have hΛi : b + n - 2 - (n - 1) + 1 = b := by omega
  rw [hΛi] at hLV

  choose! θ'' hθ'' using hP'
  set Wd := S.base.Wb (S.base.cnt w' + n * C.Kst) with hWd
  set pairs := S.base.Wb (S.base.cnt w' + C.Kst) ×ˢ S.base.Wb (S.base.cnt w' + C.Kst) with hpairs
  have hpw : ∀ x ∈ pairs, (x.1 ∈ S.base.Wall ∧ S.base.cnt x.1 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.1 + (n - 1) * C.Kst) ⊆ Wd) ∧
      (x.2 ∈ S.base.Wall ∧ S.base.cnt x.2 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.2 + (n - 1) * C.Kst) ⊆ Wd) := by
    intro x hx
    rw [hpairs, Finset.mem_product, mem_Wb_iff, mem_Wb_iff] at hx
    exact ⟨⟨hx.1.1, by omega, Wb_mono S (by omega)⟩, ⟨hx.2.1, by omega, Wb_mono S (by omega)⟩⟩
  have hpr : ∀ u, u ∈ S.base.Wall → S.base.cnt u + (n - 1) * C.Kst ≤ S.Ntop →
      TB.IsProb (S.base.Wb (S.base.cnt u + (n - 1) * C.Kst)) (θ'' u) := fun u h1 h2 => (hθ'' u h1 h2).1
  let q : crystallineComparison.V S.f → S.W → ℝ := fun σ u =>
    ∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)
  have hq : ∀ σ, TB.IsProb Wd (q σ) := by
    intro σ
    set A := crystallineComparison.pat L ((S.g : ℝ) • σ)
    refine ⟨fun u => Finset.sum_nonneg fun x hx => mul_nonneg ((hθL A).1 x) (div_nonneg (add_nonneg
      ((hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).1 u) ((hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).1 u)) (by norm_num)),
      fun u hu => Finset.sum_eq_zero fun x hx => ?_, ?_⟩
    · have h1 : θ'' x.1 u = 0 := (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).2.1 u fun h => hu ((hpw x hx).1.2.2 h)
      have h2 : θ'' x.2 u = 0 := (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).2.1 u fun h => hu ((hpw x hx).2.2.2 h)
      simp [h1, h2]
    · show ∑ u ∈ Wd, ∑ x ∈ pairs, θL A x * ((θ'' x.1 u + θ'' x.2 u) / 2) = 1
      rw [Finset.sum_comm, ← (hθL A).2.2]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib,
        prob_sum_sub (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1) (hpw x hx).1.2.2,
        prob_sum_sub (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1) (hpw x hx).2.2.2]
      norm_num
  obtain ⟨θn, hθn, hmix⟩ := tsum_mix Wd (fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst L ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))
    (fun σ => mL_nonneg _ _ hL0 _) hsm
    (by linarith [one_le_tsum_mL La C.Kst L hL0 (S.g : ℝ) hsm]) (fun σ => q σ) (fun σ => hq σ)
  refine ⟨θn, hθn, fun Y hY κ hκ z₀ Ss hS hgood => ?_⟩
  obtain ⟨Pq, Qq, hreg, hGD⟩ := germ_global S hpos hI hg Λ hLL hGL hΛ0 ε hε n hn b hb hbn w' hcnt Y hY
  obtain ⟨Lm, j1, j2, hLm⟩ := GlobalTheory.dual_smul_mem La (S.g : ℝ) hg'.ne'
  have := j1; have := j2
  set N' : S.W → ℝ := fun u => P' * S.base.N0 ε (b - 1) u Y κ with hN'
  let D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ := fun v h h' c =>
    KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, c)]) (C.loc (S.σ v) h' ++ [(n, c)])
  have hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z) := by
    intro v z _
    have := PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(n, z)])
    exact JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(n, z)])
      (fun h hh => Finset.mem_image_of_mem _ hh)
  let U : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ := fun v p q =>
    KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)]) (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])
  have hsub : ∀ x' ∈ pairs, ∀ (t : crystallineComparison.V S.f), Good t →
      (KB.NstV S ε (b + n - 2) (n - 1) x'.1 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.1 u * N' u ∧
      (KB.NstV S ε (b + n - 2) (n - 1) x'.2 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.2 u * N' u := by
    intro x' hx' t ht
    have e : b + (n - 1) - 1 = b + n - 2 := by omega
    have h1 := (hθ'' x'.1 (hpw x' hx').1.1 (hpw x' hx').1.2.1).2 Y hY κ hκ t ht
    have h2 := (hθ'' x'.2 (hpw x' hx').2.1 (hpw x' hx').2.2.1).2 Y hY κ hκ t ht
    rw [e] at h1 h2
    have s1 : ∑ u ∈ Wd, θ'' x'.1 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.1 + (n - 1) * C.Kst), θ'' x'.1 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').1.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').1.1 (hpw x' hx').1.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    have s2 : ∑ u ∈ Wd, θ'' x'.2 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.2 + (n - 1) * C.Kst), θ'' x'.2 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').2.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').2.1 (hpw x' hx').2.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    exact ⟨s1 ▸ h1, s2 ▸ h2⟩
  have hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V S.f, Good x → Good (x + (S.g : ℝ) • σ) →
      ‖phi Y κ U x (x + (S.g : ℝ) • σ)‖ ≤
        crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u := by
    intro σ _ x hx hx'
    set t : crystallineComparison.V S.f := fun v => (x v)⁻¹ with ht_def
    set t' : crystallineComparison.V S.f := fun v => ((x + (S.g : ℝ) • σ) v)⁻¹ with ht'_def
    have ht : Good t := fun v => inv_ne_zero (hx v)
    have ht' : Good t' := fun v => inv_ne_zero (hx' v)
    have ephi : phi Y κ U x (x + (S.g : ℝ) • σ) = KB.NstV S ε (b + n - 2) (n - 1) w' Y κ t t' := by
      rw [nstV_eq]; rfl
    have hlv := hLV Y κ κ κ (fun h hh => by rw [hY h hh]; omega) (blockPSD_same Y κ hκ) t t' ht ht'
      (crystallineComparison.pat L ((S.g : ℝ) • σ))
    have ediff : ∀ v, (t v)⁻¹ - (t' v)⁻¹ = -(((S.g : ℝ) • σ) v) := by
      intro v; simp only [t, t', inv_inv, Pi.add_apply]; ring
    simp only [ediff, norm_neg] at hlv
    rw [ephi]
    refine bound_mL C.Kst L hL0 _ _ _ (hlv.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun v _ => pow_nonneg (hL0 v) _)
    show _ ≤ ∑ u ∈ Wd, (∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)) * N' u
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun x' hx' => ?_
    have hs := hsub x' hx'
    have e2 : ∑ u ∈ Wd, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((θ'' x'.1 u + θ'' x'.2 u) / 2) * N' u =
        θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((∑ u ∈ Wd, θ'' x'.1 u * N' u + ∑ u ∈ Wd, θ'' x'.2 u * N' u) / 2) := by
      rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [e2]
    refine mul_le_mul_of_nonneg_left ?_ ((hθL _).1 x')
    linarith [(hs t ht).1, (hs t' ht').2]
  have hH := herglotz_germ (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1)
    (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b n)
    (fun _ => dlB_pos S hg b n) U Pq Qq
    (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) hGD
    (fun _ _ _ _ => rfl) La Lm hLm
    (fun σ : crystallineComparison.V S.f => crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u) (hmix N').1 hF z₀ Ss hS
  rw [(hmix N').2] at hH
  have hN : ∑ z ∈ Ss, Nz Y κ D z = ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re :=
    Finset.sum_congr rfl fun z hz => by
      simp only [Nz, if_pos (hgood z hz)]
      rw [nstV_eq]
      rfl
  rw [hN] at hH
  refine hH.trans (le_of_eq ?_)
  have e3 : ∑ u ∈ Wd, θn u * N' u = P' * ∑ u ∈ Wd, θn u * S.base.N0 ε (b - 1) u Y κ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
  rw [e3]
  ring

end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem gsup_succ (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2)
    (hΛt : ∀ v, 0 ≤ Λ b (n - 1) v ∧ Λ b (n - 1) v ≤ thr S b n v) (P' : ℝ) (hP' : GSup S ε b (n - 1) P')
    (hP'0 : 0 ≤ P') (Cs : ℝ) (hCs1 : 1 ≤ Cs) (hCs : SumBound S.f Cs) (B R : ℝ) (hR : 0 < R)
    (hRB : (∏ _v : Fin S.f, KB.dlB S b n) * (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
      B ^ S.f * S.base.vol b n) :
    ∃ P, 0 ≤ P ∧ P ≤ B ^ S.f * S.base.vol b n * P' ∧ GSup S ε b n P := by
  obtain ⟨i1, i2, hcov, -⟩ := pbc_lstdFacts S.f R hR
  have := i1; have := i2
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  have hL0 : ∀ v, 0 ≤ Λ b (n - 1) v := fun v => (hΛt v).1
  obtain ⟨hsm, hsle⟩ := hCs R S.g (fun v => Λ b (n - 1) v) hR hg' hL0
  set M := ∑' σ : crystallineComparison.dualSet (Lstd S.f R), crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))
  have hM0 : 0 ≤ M := tsum_nonneg fun σ => mL_nonneg _ _ hL0 _
  have hdl0 : 0 ≤ ∏ _v : Fin S.f, KB.dlB S b n := Finset.prod_nonneg fun v _ => (dlB_pos S hg b n).le
  have hsz := size_step S.f Cs hCs1 _ R S.g hdl0 hR hg' _ (thr S b n) hΛt M _ hsle hRB
  refine ⟨(∏ _v : Fin S.f, KB.dlB S b n) * M / R ^ (2 * S.f) * P', by positivity,
    mul_le_mul_of_nonneg_right hsz hP'0, ?_⟩
  intro w' hw' hcnt
  obtain ⟨θ, hθ, H⟩ := germ_step S hpos hI hg Λ hLL hGL hΛ0 ε hε n hn b hb hbn P' hP' hP'0 w' hw' hcnt
    (Lstd S.f R) hsm
  refine ⟨θ, hθ, fun Y hY κ hκ t ht => ?_⟩
  have h1 := H Y hY κ hκ t {t} (by simp) (by simpa using ht)
  rw [hcov, Finset.sum_singleton] at h1
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith [h1]

theorem gsup_all (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (X : ℕ → Fin S.f → ℝ) (hW : ∀ v, KB.WaveLoc S v fun i => X i v)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ thr S b (s + 1) v)
    (ε : ℝ) (hε : 0 < ε) (b : ℕ) (hb : 1 ≤ b)
    (hX : b ≤ S.G.r + 1 → ∀ v, 0 ≤ X b v ∧ X b v ≤ thr S b 1 v)
    (Cs : ℝ) (hCs1 : 1 ≤ Cs) (hCs : SumBound S.f Cs) (B : ℝ) (hB1 : 1 ≤ B)
    (hSz : ∀ n, 1 ≤ n → ∃ R : ℝ, 0 < R ∧
      (∏ _v : Fin S.f, KB.dlB S b n) * (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
        B ^ S.f * S.base.vol b n)
    (hvol : ∀ n, 0 ≤ S.base.vol b n) :
    ∀ n, 1 ≤ n → b + n ≤ S.G.r + 1 →
      ∃ P, 0 ≤ P ∧ P ≤ B ^ (S.f * n) * ∏ m ∈ Finset.Ico 1 (n + 1), S.base.vol b m ∧ GSup S ε b n P := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro hbn
    obtain ⟨R, hR, hRB⟩ := hSz 1 le_rfl
    obtain ⟨P, hP0, hPle, hP⟩ := gsup_one S hg hpos hI X hW ε hε b hb (by omega) (hX (by omega)) Cs hCs1 hCs
      B R hR hRB
    refine ⟨P, hP0, ?_, hP⟩
    simpa using hPle
  | succ n hn ih =>
    intro hbn
    obtain ⟨P', hP'0, hP'le, hP'⟩ := ih (by omega)
    obtain ⟨R, hR, hRB⟩ := hSz (n + 1) (by omega)
    have hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v :=
      fun b s hb hs hbs v => (hΛ b s hb hs hbs v).1
    have hΛt : ∀ v, 0 ≤ Λ b (n + 1 - 1) v ∧ Λ b (n + 1 - 1) v ≤ thr S b (n + 1) v := by
      intro v
      have := hΛ b n hb hn (by omega) v
      simpa using this
    have hP'' : GSup S ε b (n + 1 - 1) P' := by simpa using hP'
    obtain ⟨P, hP0, hPle, hP⟩ := gsup_succ S hpos hI hg Λ hLL hGL hΛ0 ε hε (n + 1) (by omega) b hb (by omega)
      hΛt P' hP'' hP'0 Cs hCs1 hCs B R hR hRB
    refine ⟨P, hP0, hPle.trans ?_, hP⟩
    rw [Finset.prod_Ico_succ_top (by omega), mul_add, mul_one, pow_add]
    have hBf : 0 ≤ B ^ S.f := pow_nonneg (by linarith) _
    have hv := hvol (n + 1)
    calc B ^ S.f * S.base.vol b (n + 1) * P' ≤ B ^ S.f * S.base.vol b (n + 1) *
        (B ^ (S.f * n) * ∏ m ∈ Finset.Ico 1 (n + 1), S.base.vol b m) :=
          mul_le_mul_of_nonneg_left hP'le (mul_nonneg hBf hv)
      _ = _ := by ring

theorem embV_ne (S : C.HidaSetting E Wp Wq) (t : E) (ht : t ≠ 0) : Good (embV S t) := fun v => (map_ne_zero (S.σ v)).mpr ht

theorem embV_inj (S : C.HidaSetting E Wp Wq) [Nonempty (Fin S.f)] : Function.Injective (embV S) := by
  intro a c h
  obtain ⟨v⟩ := ‹Nonempty (Fin S.f)›
  have h1 := congrFun h v
  exact (S.σ v).injective h1

theorem nst_eq_nstV (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i s : ℕ) (hi : i ≤ S.G.r + 1) (w : S.W)
    (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (t : E) :
    S.base.Nst ε i s w Y κ t t = KB.NstV S ε i s w Y κ (embV S t) (embV S t) := by
  unfold TB.Data.Nst KB.NstV
  simp only [C.HidaSetting.base, C.HidaSetting.mkData, C.HidaSetting.gram, if_pos hi, TB.join, C.loc, List.map_append,
    List.map_cons, List.map_nil]
  rfl

theorem sumFormConcrete_of (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hU : S6.Unram E)
    (hpos : C.ThmPPos S) (hI : KB.IntAll S) (X : ℕ → Fin S.f → ℝ) (hW : ∀ v, KB.WaveLoc S v fun i => X i v)
    (hXt : JC.HidaCurvatureBarriers S X) (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v)
    (hΛt : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ S.base.szL b s v)
    (hthr : ∀ b s v, 1 ≤ b → 1 ≤ s → 0 < J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s (S.pl v))
    (hGL : ∀ v, KB.GermLoc S v) (Cs : ℝ) (hCs1 : 1 ≤ Cs) (hCs : SumBound S.f Cs) (B : ℝ) (hB1 : 1 ≤ B)
    (hSz : ∀ b n, 1 ≤ b → 1 ≤ n → ∃ R : ℝ, 0 < R ∧
      (∏ _v : Fin S.f, KB.dlB S b n) * (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
        B ^ S.f * S.base.vol b n)
    (A : ℝ) (hA1 : 1 ≤ A)
    (hBL : ∀ b s, 1 ≤ b → 1 ≤ s →
        ∃ (_ : DiscreteTopology (latV S (J.LaB E S.g S.G.r b s)))
          (_ : IsZLattice ℝ (latV S (J.LaB E S.g S.G.r b s))),
          ZLattice.covolume (latV S (J.LaB E S.g S.G.r b s)) = ∏ _v : Fin S.f, KB.dlB S b s ∧
          (∃ (Lm : Submodule ℤ (crystallineComparison.V S.f)) (_ : DiscreteTopology Lm) (_ : IsZLattice ℝ Lm),
            ∀ σ ∈ crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)), (S.g : ℝ) • σ ∈ Lm) ∧
          ∀ Λ : Fin S.f → ℝ, (∀ v, 0 ≤ Λ v ∧ Λ v ≤ thr S b s v) → S.base.vol b s ≤ 1 →
            Summable (fun σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)) =>
              crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) ∧
            ∑' σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)),
              crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) ≤ A ^ S.f)
    (C₄ : ℝ) (hCA : A ≤ C₄) (hCB : B ≤ C₄) : JC.SumFormConcrete S C₄ := by
  have hg : 0 < S.g := Nat.mul_pos hg1 hg2
  have hne : Nonempty (Fin S.f) := ⟨S.pl.symm (Classical.arbitrary _)⟩
  have hΛ : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ thr S b (s + 1) v := by
    intro b s hb hs hbs v
    have := hΛt b s hb hs hbs v
    refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
    show (if b + s ≤ S.G.r + 1 then J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b (s + 1) (S.pl v)
      else 2 * J.thrP S.G S.CA S.de S.de' S.T S.T' S.l b (S.pl v)) = _
    rw [if_pos hbs]; rfl
  have hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v :=
    fun b s hb hs hbs v => (hΛ b s hb hs hbs v).1
  have hvol : ∀ b n, 0 ≤ S.base.vol b n := by
    intro b n
    show 0 ≤ (∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b n w) ^ 2 /
      (FractionalIdeal.absNorm (S6.dualIdl E S.g (S6.nuBlock S.G.r b n)) : ℝ)
    exact div_nonneg (sq_nonneg _) (by first | exact_mod_cast FractionalIdeal.absNorm_nonneg _ | exact Rat.cast_nonneg.2 (FractionalIdeal.absNorm_nonneg _) | positivity)
  intro ε hε i s hs hsi hir w hw hbud hvolS
  have hir' : i ≤ S.G.r + 1 := hir
  set b := i - s + 1 with hbdef
  have hb : 1 ≤ b := by omega
  have hbi : b + s - 1 = i := by omega

  obtain ⟨P', hP'0, hP'le, hP'⟩ := gsup_all S hpos hI hg X hW Λ hLL hGL hΛ ε hε b hb
    (fun hbr v => hXt b hb hbr v) Cs hCs1 hCs B hB1 (fun n hn => hSz b n hb hn) (hvol b) (s - 1) (by omega)
    (by omega)

  obtain ⟨i1, i2, hcov, ⟨Lm, j1, j2, hLm⟩, hsum⟩ := hBL b s hb (by omega)
  have := i1; have := i2
  have hΛs : ∀ v, 0 ≤ Λ b (s - 1) v ∧ Λ b (s - 1) v ≤ thr S b s v := by
    intro v
    have := hΛ b (s - 1) hb (by omega) (by omega) v
    rwa [show s - 1 + 1 = s by omega] at this
  obtain ⟨hsm, hsle⟩ := hsum (fun v => Λ b (s - 1) v) hΛs hvolS
  have hcnt : S.base.cnt w + s * C.Kst ≤ S.Ntop := by
    have h1 : S.base.cnt w + (s + 1) * S.base.K ≤ S.base.Ntop := hbud
    have h2 : S.base.K = C.Kst := rfl
    have h3 : S.base.Ntop = S.Ntop := rfl
    rw [h2, h3] at h1
    have : s * C.Kst ≤ (s + 1) * C.Kst := Nat.mul_le_mul_right _ (by omega)
    omega
  have hP'' : GSup S ε b (s - 1) P' := hP'
  obtain ⟨θ, hθ, H⟩ := germ_step S hpos hI hg Λ hLL hGL hΛ0 ε hε s hs b hb (by omega) P' hP'' hP'0 w hw hcnt
    (latV S (J.LaB E S.g S.G.r b s)) hsm
  set M := ∑' σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)),
    crystallineComparison.mL C.Kst (fun v => Λ b (s - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))
  have hM0 : 0 ≤ M := tsum_nonneg fun σ => mL_nonneg _ _ (fun v => (hΛs v).1) _
  refine ⟨M * P', ?_, θ, hθ, fun Y hY κ hκ t₀ Ss hS => ?_⟩
  · have hpv : 0 ≤ ∏ m ∈ Finset.Ico 1 s, S.base.vol b m := Finset.prod_nonneg fun m _ => hvol b m
    have e1 : s - 1 + 1 = s := by omega
    rw [e1] at hP'le
    have hC0 : 0 ≤ C₄ := by linarith
    calc M * P' ≤ A ^ S.f * (B ^ (S.f * (s - 1)) * ∏ m ∈ Finset.Ico 1 s, S.base.vol b m) :=
          mul_le_mul hsle hP'le hP'0 (pow_nonneg (by linarith) _)
      _ ≤ C₄ ^ S.f * (C₄ ^ (S.f * (s - 1)) * ∏ m ∈ Finset.Ico 1 s, S.base.vol b m) := by
          gcongr
      _ = C₄ ^ (S.base.f * s) * ∏ m ∈ Finset.Ico 1 s, S.base.vol b m := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          show S.f + S.f * (s - 1) = S.f * s
          have : s = (s - 1) + 1 := by omega
          conv_rhs => rw [this]
          ring
  · have hY' : ∀ h ∈ Y, TB.level h = b - 1 := by
      intro h hh; rw [hY h hh]; omega
    have hmem : ∀ z ∈ Ss.image (embV S), z - embV S t₀ ∈ latV S (J.LaB E S.g S.G.r b s) := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hz
      rw [← map_sub]
      exact Submodule.mem_map_of_mem (hS t ht).2
    have hgd : ∀ z ∈ Ss.image (embV S), Good z := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hz
      exact embV_ne S t (hS t ht).1
    have h1 := H Y hY' κ hκ (embV S t₀) (Ss.image (embV S)) hmem hgd
    rw [hcov, Finset.sum_image fun a _ b _ h => embV_inj S h] at h1
    have hdl : 0 < ∏ _v : Fin S.f, KB.dlB S b s := Finset.prod_pos fun v _ => dlB_pos S hg b s
    have e2 : ∀ t ∈ Ss, (S.base.Nst ε i s w Y κ t t).re =
        (KB.NstV S ε (b + s - 1) s w Y κ (embV S t) (embV S t)).re := by
      intro t _
      rw [hbi, nst_eq_nstV S ε i s hir' w Y κ t]
    rw [Finset.sum_congr rfl e2]
    have e3 : i - s = b - 1 := by omega
    rw [e3]
    have h1' : (∏ _v : Fin S.f, KB.dlB S b s) *
        ∑ x ∈ Ss, (KB.NstV S ε (b + s - 1) s w Y κ ((embV S) x) ((embV S) x)).re ≤
        (∏ _v : Fin S.f, KB.dlB S b s) * ((M * P') *
          ∑ u ∈ S.base.Wb (S.base.cnt w + s * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ) := by
      rw [← mul_assoc]; exact h1
    exact le_of_mul_le_mul_left h1' hdl

end setting

theorem sumFormOfLoc : KB.SumFormOfLoc := by
  obtain ⟨Cs, hCs1, hCs⟩ := pbc_lstdSum
  obtain ⟨B, hB1, hSzAll⟩ := pbc_sizesSup Cs hCs1
  obtain ⟨A, hA1, hBLall⟩ := pbc_blockLatV
  refine ⟨max A B, le_max_of_le_left hA1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ S X Λ hg1 hg2 hU hpos hG hI hW hXt hL hΛt hthr hGL
  exact sumFormConcrete_of S hg1 hg2 hU hpos hI X hW hXt Λ hL hΛt hthr hGL Cs hCs1
    (fun R g L hR hg hL => hCs S.f R g L hR hg hL) B hB1
    (fun b n hb hn => hSzAll E Wp Wq S hg1 hg2 hU b n hb hn fun v => hthr b n v hb hn) A hA1
    (fun b s hb hs => hBLall E Wp Wq S hg1 hg2 hU b s hb hs) (max A B) (le_max_left _ _) (le_max_right _ _)

end

end Formalism.FourierDecayAlt.P.PBC

namespace Formalism.FourierDecayAlt.P

theorem sum_form_of_local_statements : Formalism.FourierDecayAlt.KB.SumFormOfLoc := PBC.sumFormOfLoc

end Formalism.FourierDecayAlt.P
end
