import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZeroDimA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant

section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def mulR (c : M2 n) : M2 n →L[ℂ] M2 n := (LinearMap.mulRight ℂ c).toContinuousLinearMap

theorem mulR_apply (c y : M2 n) : mulR c y = y * c := rfl

def mulL (c : M2 n) : M2 n →L[ℂ] M2 n := (LinearMap.mulLeft ℂ c).toContinuousLinearMap

theorem mulL_apply (c y : M2 n) : mulL c y = c * y := rfl

theorem iterated_fderiv_right_translation {N : ℕ} (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (W : Fin (N + 1) → M2 n) (hW : ∀ a b, W a * W b = 0) (x : M2 n) (hx : x ∈ U) :
    fderiv ℂ (fun y => iteratedFDeriv ℂ N F y (fun i => y * W i.succ)) x (x * W 0) =
      iteratedFDeriv ℂ (N + 1) F x (fun i => x * W i) := by
  classical
  have hFx : ContDiffAt ℂ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ N F) x :=
    hFx.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top N)
  have hg : ∀ i : Fin N, HasFDerivAt (fun y : M2 n => y * W i.succ) (mulR (W i.succ)) x :=
    fun i => (mulR (W i.succ)).hasFDerivAt
  have h := hd.hasFDerivAt.continuousMultilinearMap_apply (g := fun i y => y * W i.succ) hg
  have hz : ∀ i : Fin N, mulR (W i.succ) (x * W 0) = 0 := fun i => by
    rw [mulR_apply, mul_assoc, hW, mul_zero]
  refine (congrArg (fun L => L (x * W 0)) h.fderiv).trans ?_
  have hs : ∀ L : Fin N → (M2 n →L[ℂ] ℂ), (∀ i, L i (x * W 0) = 0) → (∑ i, L i) (x * W 0) = 0 := by
    intro L hL
    rw [ContinuousLinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hL i
  rw [ContinuousLinearMap.add_apply, hs _ (fun i => by rw [ContinuousLinearMap.comp_apply, hz, map_zero]), add_zero,
    ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply, iteratedFDeriv_succ_apply_left]
  rfl

def rit (F : M2 n → ℂ) : (N : ℕ) → (Fin N → M2 n) → M2 n → ℂ
  | 0, _ => F
  | N + 1, W => fun y => fderiv ℂ (rit F N (fun i => W i.succ)) y (y * W 0)

theorem rit_zero (F : M2 n → ℂ) (W : Fin 0 → M2 n) : rit F 0 W = F := rfl

theorem rit_succ (F : M2 n → ℂ) (N : ℕ) (W : Fin (N + 1) → M2 n) :
    rit F (N + 1) W = fun y => fderiv ℂ (rit F N (fun i => W i.succ)) y (y * W 0) := rfl

theorem rit_contDiffOn (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) :
    ∀ (N : ℕ) (W : Fin N → M2 n), ContDiffOn ℂ ∞ (rit F N W) U := by
  intro N
  induction N with
  | zero => intro W; exact hF
  | succ N ih =>
    intro W
    rw [rit_succ]
    exact ((ih _).fderiv_of_isOpen hU (by simp)).clm_apply ((mulR (W 0)).contDiff.contDiffOn)

theorem rit_eq (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) :
    ∀ (N : ℕ) (W : Fin N → M2 n), (∀ a b, W a * W b = 0) → ∀ x ∈ U,
      rit F N W x = iteratedFDeriv ℂ N F x (fun i => x * W i) := by
  intro N
  induction N with
  | zero =>
    intro W _ x _
    simp [rit_zero, iteratedFDeriv_zero_apply]
  | succ N ih =>
    intro W hW x hx
    rw [rit_succ]
    have hev : rit F N (fun i => W i.succ) =ᶠ[nhds x]
        (fun y => iteratedFDeriv ℂ N F y (fun i => y * W i.succ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih _ (fun a b => hW _ _) y hy
    simp only
    rw [hev.fderiv_eq]
    exact iterated_fderiv_right_translation F U hU hF W hW x hx

theorem rit_law (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (χ : M2 n → ℂ)
    (hUP : ∀ P x, InP P → x ∈ U → P * x ∈ U) (hl : ∀ P x, InP P → x ∈ U → F (P * x) = χ P * F x) :
    ∀ (N : ℕ) (W : Fin N → M2 n) (P x : M2 n), InP P → x ∈ U → rit F N W (P * x) = χ P * rit F N W x := by
  intro N
  induction N with
  | zero => intro W P x hP hx; exact hl P x hP hx
  | succ N ih =>
    intro W P x hP hx
    rw [rit_succ]
    simp only
    set H := rit F N (fun i => W i.succ) with hH
    have hHs : ContDiffOn ℂ ∞ H U := rit_contDiffOn F U hU hF N _
    have hPx : P * x ∈ U := hUP P x hP hx
    have hdH : DifferentiableAt ℂ H (P * x) :=
      (hHs.contDiffAt (hU.mem_nhds hPx)).differentiableAt (by simp)
    have hev : (fun y => H (P * y)) =ᶠ[nhds x] (fun y => χ P * H y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih _ P y hP hy
    have hc : fderiv ℂ (fun y => H (P * y)) x = (fderiv ℂ H (P * x)).comp (mulL P) := by
      have := (hdH.hasFDerivAt.comp x (mulL P).hasFDerivAt)
      exact this.fderiv
    have hdHx : DifferentiableAt ℂ H x :=
      (hHs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have e1 : fderiv ℂ H (P * x) (P * x * W 0) = fderiv ℂ (fun y => H (P * y)) x (x * W 0) := by
      rw [hc]; simp [mulL_apply, mul_assoc]
    rw [e1]
    refine (congrArg (fun L : M2 n →L[ℂ] ℂ => L (x * W 0)) hev.fderiv_eq).trans ?_
    have hcm : fderiv ℂ (fun y => χ P * H y) x = χ P • fderiv ℂ H x := fderiv_const_mul hdHx (χ P)
    refine (congrArg (fun L : M2 n →L[ℂ] ℂ => L (x * W 0)) hcm).trans ?_
    simp

theorem snoc_rev {N : ℕ} (W : Fin (N + 1) → M2 n) :
    (Fin.snoc (fun i : Fin N => W (Fin.rev i).succ) (W 0) : Fin (N + 1) → M2 n) = fun i => W (Fin.rev i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Fin.snoc_last]
  · simp [Fin.snoc_castSucc, Fin.rev_castSucc]

theorem rit_snoc (G : M2 n → ℂ) (c : M2 n) :
    ∀ (N : ℕ) (V : Fin N → M2 n), rit (fun y => fderiv ℂ G y (y * c)) N V = rit G (N + 1) (Fin.snoc V c) := by
  intro N
  induction N with
  | zero =>
    intro V
    funext y
    simp only [rit_zero, rit_succ]
    rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]
  | succ N ih =>
    intro V
    rw [rit_succ, rit_succ, ih]
    have h1 : (fun i : Fin (N + 1) => (Fin.snoc V c : Fin (N + 2) → M2 n) i.succ) =
        Fin.snoc (fun i : Fin N => V i.succ) c := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_last]
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    have h0 : (Fin.snoc V c : Fin (N + 2) → M2 n) 0 = V 0 := by
      simpa using (Fin.snoc_castSucc (α := fun _ => M2 n) (p := V) (x := c) (i := 0))
    rw [h1, h0]

theorem cont_on_K (H : M2 n → ℂ) (hH : ContDiffOn ℂ ∞ H (Dom n)) (Kg : Type) [TopologicalSpace Kg]
    (ι : Kg → M2 n) (hι : Continuous ι) (hdom : ∀ k, ι k ∈ Dom n) : Continuous (fun k => H (ι k)) :=
  hH.continuousOn.comp_continuous hι hdom

theorem rit_transpose (hI : InfInv) (F1 : M2 n → ℂ) (χ1 χ2 : M2 n → ℂ) (hF1 : ContDiffOn ℂ ∞ F1 (Dom n))
    (h1 : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = χ1 P * F1 x)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) :
    ∀ (N : ℕ) (F2 : M2 n → ℂ), ContDiffOn ℂ ∞ F2 (Dom n) →
      (∀ P x, InP P → x ∈ Dom n → F2 (P * x) = χ2 P * F2 x) → ∀ (W : Fin N → M2 n), (∀ a b, W a * W b = 0) →
      ∫ k, rit F1 N W (ι k) * F2 (ι k) ∂μ = (-1) ^ N * ∫ k, F1 (ι k) * rit F2 N (fun i => W (Fin.rev i)) (ι k) ∂μ := by
  have hdom : ∀ k, ι k ∈ Dom n := fun k => gset_sub_dom ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hint : ∀ g : Kg → ℂ, Continuous g → Integrable g μ := fun g hg => by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall fun k => hC k trivial)
  have hUP : ∀ P x, InP P → x ∈ Dom n → P * x ∈ Dom n := fun P x hP hx => mul_mem_dom hP hx
  intro N
  induction N with
  | zero => intro F2 _ _ W _; simp [rit_zero]
  | succ N ih =>
    intro F2 hF2 h2 W hW
    set G := rit F1 N (fun i => W i.succ) with hGdef
    set F2' : M2 n → ℂ := fun y => fderiv ℂ F2 y (y * W 0) with hF2'def
    have hG : ContDiffOn ℂ ∞ G (Dom n) := rit_contDiffOn F1 _ isOpen_dom hF1 N _
    have hGlaw : ∀ P x, InP P → x ∈ Dom n → G (P * x) = χ1 P * G x :=
      rit_law F1 (Dom n) isOpen_dom hF1 χ1 hUP h1 N _
    have hF2'e : F2' = rit F2 1 (fun _ => W 0) := rfl
    have hF2' : ContDiffOn ℂ ∞ F2' (Dom n) := by rw [hF2'e]; exact rit_contDiffOn F2 _ isOpen_dom hF2 1 _
    have hF2'law : ∀ P x, InP P → x ∈ Dom n → F2' (P * x) = χ2 P * F2' x := by
      rw [hF2'e]; exact rit_law F2 (Dom n) isOpen_dom hF2 χ2 hUP h2 1 _
    have hlaw : ∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x →
        G (p * x) * F2 (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * (G x * F2 x) := by
      intro p x hp hp0 hx
      have hP : InP p := ⟨hp, hp0⟩
      rw [hGlaw p x hP (gset_sub_dom hx), h2 p x hP (gset_sub_dom hx), ← h12 p hP]
      ring
    have hInf := hI n G F2 (Dom n) isOpen_dom gset_sub_dom hG hF2 hlaw Kg μ ι hι hK (W 0)
    have hA : Continuous (fun k => rit F1 (N + 1) W (ι k) * F2 (ι k)) :=
      (cont_on_K _ (rit_contDiffOn F1 _ isOpen_dom hF1 (N + 1) W) Kg ι hι hdom).mul
        (cont_on_K _ hF2 Kg ι hι hdom)
    have hB : Continuous (fun k => G (ι k) * F2' (ι k)) :=
      (cont_on_K _ hG Kg ι hι hdom).mul (cont_on_K _ hF2' Kg ι hι hdom)
    have hsplit : (∫ k, rit F1 (N + 1) W (ι k) * F2 (ι k) ∂μ) + ∫ k, G (ι k) * F2' (ι k) ∂μ = 0 := by
      rw [← integral_add (hint _ hA) (hint _ hB)]
      exact hInf
    have hIH := ih F2' hF2' hF2'law (fun i => W i.succ) (fun a b => hW _ _)
    have hr : rit F2' N (fun i => W (Fin.rev i).succ) = rit F2 (N + 1) (fun i => W (Fin.rev i)) := by
      rw [hF2'def, rit_snoc F2 (W 0) N, snoc_rev]
    rw [hr] at hIH
    rw [pow_succ]
    linear_combination hsplit - hIH

end PositivityTheory.Rg.Sw.LVs
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def WD (Q R : Matrix (Fin n) (Fin n) ℂ) : M2 n := Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹

theorem mX_eq (Q R : Matrix (Fin n) (Fin n) ℂ) : mX 1 Q R 1 = 1 + WD Q R := mX_eq' Q R

theorem WD_mul_WD_B_A (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
    (T' : Matrix (blkA (n := n) j) (blkA j) ℂ) (S' : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    WD (embOn (blkB j) S) (embOn (blkA j) T) * WD (embOn (blkB j) S') (embOn (blkA j) T') = 0 := by
  have h1 : embOn (blkB j) S * embOn (blkA j) T' = 0 :=
    embOn_mul_embOn_disj (fun c hc hc' => by
      simp only [blkB, Finset.mem_compl] at hc
      exact hc hc') S T'
  have h2 : embOn (blkA j) T * embOn (blkB j) S' = 0 :=
    embOn_mul_embOn_disj (fun c hc hc' => by
      simp only [blkB, Finset.mem_compl] at hc'
      exact hc' hc) T S'
  simp only [WD]
  rw [WD_prod, h1, h2]
  simp

theorem contDiffOn_scalar_section (p q : ℤ) : ContDiffOn ℂ ∞ (f0 (n := n) p q) {x | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} :=
  contDiffOn_scalar_section_of_units p q

theorem contDiffOn_hF (j : ℕ) (p q : ℤ) : ContDiffOn ℂ ∞ (hF (n := n) j p q) (Dom n) := contDiffOn_hF' j p q

theorem contDiffOn_fV (p q : ℤ) : ContDiffOn ℂ ∞ (fV (n := n) p q) (Dom n) := contDiffOn_fV' p q

private theorem contDiffOn_iteratedFDeriv_apply {E G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (F : E → G) (U : Set E) (hU : IsOpen U)
    (hF : ContDiffOn ℂ ∞ F U) (b : ℕ) (w : Fin b → E) :
    ContDiffOn ℂ ∞ (fun y => iteratedFDeriv ℂ b F y w) U := by
  intro y hy
  have h := (hF.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (i := b) (m := ∞)
    (by exact_mod_cast le_top)
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin b => E) G w).contDiff.contDiffAt.comp y h).contDiffWithinAt

private theorem iteratedFDeriv_add_append_eq_iteratedFDeriv_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a b : ℕ) :
    ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] (F : E → G) (U : Set E), IsOpen U →
      ContDiffOn ℂ ∞ F U → ∀ x ∈ U, ∀ (u : Fin a → E) (w : Fin b → E),
      iteratedFDeriv ℂ (a + b) F x (Fin.append u w) =
        iteratedFDeriv ℂ a (fun y => iteratedFDeriv ℂ b F y w) x u := by
  induction b with
  | zero =>
    intro G _ _ F U hU hF x hx u w
    have hw : Fin.append u w = u := by
      funext i
      exact Fin.append_left u w i
    rw [hw]
    simp only [iteratedFDeriv_zero_apply]
    rfl
  | succ b ih =>
    intro G _ _ F U hU hF x hx u w
    have hF' : ContDiffOn ℂ ∞ (fderiv ℂ F) U := hF.fderiv_of_isOpen hU (by exact_mod_cast le_top)
    let v : Fin (a + b + 1) → E := @Fin.append a (b + 1) E u w
    have h1 : iteratedFDeriv ℂ (a + (b + 1)) F x (Fin.append u w) =
        iteratedFDeriv ℂ (a + b) (fun y => fderiv ℂ F y) x (Fin.init v) (v (Fin.last (a + b))) :=
      iteratedFDeriv_succ_apply_right v
    have hinit : Fin.init v = Fin.append u (Fin.init w) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact Fin.append_left u w j
      · rw [Fin.append_right]
        exact Fin.append_right u w j.castSucc
    have hlast : v (Fin.last (a + b)) = w (Fin.last b) := Fin.append_right u w (Fin.last b)
    rw [h1, hinit, hlast, ih (fderiv ℂ F) U hU hF' x hx u (Fin.init w)]
    have hfun : (fun y => iteratedFDeriv ℂ (b + 1) F y w) =
        (ContinuousLinearMap.apply ℂ G (w (Fin.last b))) ∘
          (fun y => iteratedFDeriv ℂ b (fun z => fderiv ℂ F z) y (Fin.init w)) := by
      funext y
      simp [iteratedFDeriv_succ_apply_right]
    have hs : ContDiffAt ℂ ∞ (fun y => iteratedFDeriv ℂ b (fun z => fderiv ℂ F z) y (Fin.init w)) x :=
      (contDiffOn_iteratedFDeriv_apply (fderiv ℂ F) U hU hF' b (Fin.init w)).contDiffAt (hU.mem_nhds hx)
    rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_left _ hs (by exact_mod_cast le_top)]
    rfl

private theorem iteratedFDeriv_comp_add_clm_zero {E E' G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (F : E → G) (U : Set E) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (y : E) (hy : y ∈ U)
    (L : E' →L[ℂ] E) (b : ℕ) (v : Fin b → E') :
    iteratedFDeriv ℂ b (fun S => F (y + L S)) 0 v = iteratedFDeriv ℂ b F y (fun i => L (v i)) := by
  let F' : E → G := fun z => F (y + z)
  let U' : Set E := {z | y + z ∈ U}
  have hU' : IsOpen U' := hU.preimage (continuous_const.add continuous_id)
  have hF' : ContDiffOn ℂ ∞ F' U' :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)
  have h0 : L 0 ∈ U' := by
    show y + L 0 ∈ U
    simpa using hy
  have hpre : IsOpen (L ⁻¹' U') := hU'.preimage L.continuous
  have key := L.iteratedFDerivWithin_comp_right hF' hU'.uniqueDiffOn hpre.uniqueDiffOn h0 (i := b)
    (by exact_mod_cast le_top)
  have e1 : iteratedFDerivWithin ℂ b (F' ∘ L) (L ⁻¹' U') 0 = iteratedFDeriv ℂ b (F' ∘ L) 0 :=
    iteratedFDerivWithin_of_isOpen b hpre h0
  have e2 : iteratedFDerivWithin ℂ b F' U' (L 0) = iteratedFDeriv ℂ b F' (L 0) :=
    iteratedFDerivWithin_of_isOpen b hU' h0
  have key2 : iteratedFDeriv ℂ b (F' ∘ L) 0 =
      (iteratedFDeriv ℂ b F' (L 0)).compContinuousLinearMap fun _ => L := by
    rw [← e1, ← e2]
    exact key
  have e3 : iteratedFDeriv ℂ b F' (L 0) = iteratedFDeriv ℂ b F y := by
    have := iteratedFDerivWithin_comp_add_left (𝕜 := ℂ) (f := F) (s := Set.univ) b y (L 0)
    simp only [iteratedFDerivWithin_univ, Set.vadd_set_univ, map_zero, add_zero] at this
    rw [map_zero]
    exact this
  have hfun : (fun S => F (y + L S)) = F' ∘ L := rfl
  rw [hfun, key2, e3]
  rfl

theorem detD_detD_comp {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (x₀ : M2 n) (hx : x₀ ∈ U)
    (LA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : Matrix ιB ιB ℂ →L[ℂ] M2 n) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) F x₀
          (Fin.append (fun i => LA (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
  have hΨ : ∀ τ : Equiv.Perm ιB, ContDiffOn ℂ ∞ (fun y => iteratedFDeriv ℂ (Fintype.card ιB) F y
      (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) U :=
    fun τ => contDiffOn_iteratedFDeriv_apply F U hU hF _ _
  have hx' : x₀ + LA 0 ∈ U := by simpa using hx
  have hev : (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) =ᶠ[nhds 0]
      (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
        (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    have hopen : IsOpen {T : Matrix ιA ιA ℂ | x₀ + LA T ∈ U} :=
      hU.preimage (continuous_const.add LA.continuous)
    filter_upwards [hopen.mem_nhds hx'] with T hT
    simp only [detD]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    exact congrArg _ (iteratedFDeriv_comp_add_clm_zero F U hU hF (x₀ + LA T) hT LB _ _)
  have hD : iteratedFDeriv ℂ (Fintype.card ιA) (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) 0 =
      iteratedFDeriv ℂ (Fintype.card ιA) (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 := by
    have h2 := hev
    rw [← nhdsWithin_univ] at h2
    have := h2.iteratedFDerivWithin_eq (𝕜 := ℂ) hev.eq_of_nhds (Fintype.card ιA)
    simpa only [iteratedFDerivWithin_univ] using this
  have hsum : ∀ u : Fin (Fintype.card ιA) → Matrix ιA ιA ℂ,
      iteratedFDeriv ℂ (Fintype.card ιA) (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 u =
      ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) F x₀
        (Fin.append (fun i => LA (u i))
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    intro u
    have hcd' : ∀ τ : Equiv.Perm ιB, ContDiffAt ℂ (Fintype.card ιA) (fun T => iteratedFDeriv ℂ (Fintype.card ιB) F
        (x₀ + LA T) (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i)
          (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 := by
      intro τ
      have h1 := (hΨ τ).contDiffAt (hU.mem_nhds hx')
      have h2 : ContDiffAt ℂ ∞ (fun T : Matrix ιA ιA ℂ => x₀ + LA T) 0 :=
        (contDiff_const.add LA.contDiff).contDiffAt
      refine (h1.comp 0 h2).of_le ?_
      exact_mod_cast le_top
    have hcd : ∀ τ ∈ (Finset.univ : Finset (Equiv.Perm ιB)), ContDiffAt ℂ (Fintype.card ιA)
        (fun T => (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 :=
      fun τ _ => contDiffAt_const.mul (hcd' τ)
    rw [iteratedFDeriv_fun_sum_apply hcd, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    have hfun : (fun T => (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) =
        (Equiv.Perm.sign τ : ℂ) • (fun T => iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
      funext T
      simp
    rw [hfun, iteratedFDeriv_const_smul_apply (hcd' τ), ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    congr 1
    exact (iteratedFDeriv_comp_add_clm_zero _ U hU (hΨ τ) x₀ hx LA _ _).trans
      (iteratedFDeriv_add_append_eq_iteratedFDeriv_apply _ _ F U hU hF x₀ hx _ _).symm
  have hdef : ∀ G : Matrix ιA ιA ℂ → ℂ, detD G = ∑ σ : Equiv.Perm ιA, (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card ιA) G 0
        (fun i => Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1) :=
    fun G => rfl
  rw [hdef (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))), hD]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  ring

theorem iteratedFDeriv_right {N : ℕ} (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (W : Fin (N + 1) → M2 n) (hW : ∀ a b, W a * W b = 0) (x : M2 n) (hx : x ∈ U) :
    fderiv ℂ (fun y => iteratedFDeriv ℂ N F y (fun i => y * W i.succ)) x (x * W 0) =
      iteratedFDeriv ℂ (N + 1) F x (fun i => x * W i) :=
  iterated_fderiv_right_translation F U hU hF W hW x hx

private theorem isOpen_dom_analytic_determinants : IsOpen (Dom n) := by
  have hdet : Continuous (fun x : M2 n => x.det) := continuous_id.matrix_det
  have hS0 : IsOpen {x : M2 n | x.det ≠ 0} := isOpen_ne_fun hdet continuous_const
  have hc1 : Continuous (fun x : M2 n => (u1 x).det) := by
    apply Continuous.matrix_det
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [u1, Matrix.add_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
    fun_prop
  have hc2 : Continuous (fun x : M2 n => (u2 x).det) := by
    apply Continuous.matrix_det
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply,
      smul_eq_mul]
    fun_prop
  have h4 : IsOpen ({x : M2 n | x.det ≠ 0} ∩ (fun x => ub1 x) ⁻¹' {m | m.det ≠ 0}) :=
    continuousOn_inverse_first_block.isOpen_inter_preimage hS0 (isOpen_ne_fun continuous_id.matrix_det continuous_const)
  have he : Dom n = {x : M2 n | (u1 x).det ≠ 0} ∩ {x : M2 n | (u2 x).det ≠ 0} ∩
      ({x : M2 n | x.det ≠ 0} ∩ (fun x => ub1 x) ⁻¹' {m | m.det ≠ 0}) := by
    ext x
    simp only [Dom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, isUnit_iff_ne_zero]
    tauto
  rw [he]
  exact ((isOpen_ne_fun hc1 continuous_const).inter (isOpen_ne_fun hc2 continuous_const)).inter h4

private theorem mem_dom_of_inG {x : M2 n} (hx : InG x) : x ∈ Dom n := by
  refine ⟨isUnit_det_of_inG' hx, det_first_cayley_block_ne_zero hx, det_second_cayley_block_ne_zero hx, ?_⟩
  rw [inverse_first_block_eq_of_group hx, det_conjTranspose]
  exact star_ne_zero.mpr (det_first_cayley_block_ne_zero hx)

private theorem mul_mem_dom_of_inP {P x : M2 n} (hP : InP P) (hx : x ∈ Dom n) : P * x ∈ Dom n := by
  obtain ⟨hG, h21⟩ := hP
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  have hPu := isUnit_det_of_inG' hG
  have hrel := congrArg Matrix.det (par_rel hG h21)
  rw [det_mul, det_one, det_conjTranspose] at hrel
  have h22 : (toBlocks₂₂ P).det ≠ 0 := right_ne_zero_of_mul_eq_one hrel
  have h11 : (toBlocks₁₁ P).det ≠ 0 := by
    have := left_ne_zero_of_mul_eq_one hrel
    exact fun h => this (by rw [h, star_zero])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [det_mul]
    exact hPu.mul hx0
  · rw [automorphy_first_mul_parabolic x h21, det_mul]
    exact mul_ne_zero h22 hx1
  · rw [automorphy_second_mul_parabolic x h21, det_mul]
    exact mul_ne_zero h22 hx2
  · rw [inverse_first_block_mul_parabolic h21 hPu, det_mul]
    refine mul_ne_zero hx3 ?_
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr h11)).ne_zero

private theorem contDiffOn_fderiv_apply_mul_right {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) (Z : M2 n) :
    ContDiffOn ℂ ∞ (fun x => fderiv ℂ G x (x * Z)) (Dom n) := by
  intro x hx
  have hcd : ContDiffAt ℂ ∞ G x := hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)
  have h1 := hcd.fderiv_right (m := ∞) (by simp)
  have h2 : ContDiffAt ℂ ∞ (fun x : M2 n => x * Z) x :=
    ((LinearMap.mulRight ℂ Z).toContinuousLinearMap).contDiff.contDiffAt
  exact (h1.clm_apply h2).contDiffWithinAt

private theorem eqOn_fderiv_apply_mul_of_eqOn {G1 G2 : M2 n → ℂ} (h : Set.EqOn G1 G2 (Dom n)) (Z : M2 n) :
    Set.EqOn (fun x => fderiv ℂ G1 x (x * Z)) (fun x => fderiv ℂ G2 x (x * Z)) (Dom n) := by
  intro x hx
  have : G1 =ᶠ[nhds x] G2 := Filter.eventuallyEq_of_mem (isOpen_dom_analytic_determinants.mem_nhds hx) h
  simp only [Filter.EventuallyEq.fderiv_eq (𝕜 := ℂ) this]

private theorem fderiv_apply_mul_equivariant_of_equivariant {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) {P : M2 n} (hP : InP P) (c : ℂ)
    (h : ∀ x ∈ Dom n, G (P * x) = c * G x) (Z : M2 n) :
    ∀ x ∈ Dom n, fderiv ℂ G (P * x) (P * x * Z) = c * fderiv ℂ G x (x * Z) := by
  intro x hx
  let L : M2 n →L[ℂ] M2 n := (LinearMap.mulLeft ℂ P).toContinuousLinearMap
  have hPx : P * x ∈ Dom n := mul_mem_dom_of_inP hP hx
  have hd1 : DifferentiableAt ℂ G (L x) :=
    (hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hPx)).differentiableAt (by simp)
  have hd2 : DifferentiableAt ℂ G x := (hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)).differentiableAt (by simp)
  have heq : (G ∘ L) =ᶠ[nhds x] (fun y => c * G y) :=
    Filter.eventually_of_mem (isOpen_dom_analytic_determinants.mem_nhds hx) (fun y hy => h y hy)
  have hA : HasFDerivAt (G ∘ L) ((fderiv ℂ G (L x)).comp L) x := hd1.hasFDerivAt.comp x L.hasFDerivAt
  have hA' : HasFDerivAt (fun y => c * G y) ((fderiv ℂ G (L x)).comp L) x := hA.congr_of_eventuallyEq heq.symm
  have hB : HasFDerivAt (fun y => c * G y) (c • fderiv ℂ G x) x := hd2.hasFDerivAt.const_mul c
  have e3 := hA'.unique hB
  have e4 : ((fderiv ℂ G (L x)).comp L) (x * Z) = (c • fderiv ℂ G x) (x * Z) := by rw [e3]
  rw [Matrix.mul_assoc]
  exact e4

private theorem fderiv_fderiv_mul_comm_of_mul_zero {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) {a b : M2 n} (hab : a * b = 0)
    (hba : b * a = 0) :
    ∀ x ∈ Dom n, fderiv ℂ (fun y => fderiv ℂ G y (y * b)) x (x * a) =
      fderiv ℂ (fun y => fderiv ℂ G y (y * a)) x (x * b) := by
  intro x hx
  have hcd : ContDiffAt ℂ ∞ G x := hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)
  have hsym : IsSymmSndFDerivAt ℂ G x := hcd.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  have hdd : DifferentiableAt ℂ (fderiv ℂ G) x :=
    (hcd.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have key : ∀ c d : M2 n, c * d = 0 →
      fderiv ℂ (fun y => fderiv ℂ G y (y * d)) x (x * c) = fderiv ℂ (fderiv ℂ G) x (x * c) (x * d) := by
    intro c d hcd0
    let R : M2 n →L[ℂ] M2 n := (LinearMap.mulRight ℂ d).toContinuousLinearMap
    have hfd := hdd.hasFDerivAt.clm_apply R.hasFDerivAt
    have h0 : R (x * c) = 0 := by
      show x * c * d = 0
      rw [Matrix.mul_assoc, hcd0, Matrix.mul_zero]
    have e1 : fderiv ℂ (fun y => fderiv ℂ G y (y * d)) x (x * c) =
        fderiv ℂ G x (R (x * c)) + fderiv ℂ (fderiv ℂ G) x (x * c) (R x) :=
      congrArg (fun T => T (x * c)) hfd.fderiv
    rw [e1, h0, map_zero, zero_add]
    rfl
  rw [key a b hab, key b a hba]
  exact hsym.eq _ _

private theorem iteratedFDeriv_succ_mul_eq_fderiv_of_mul_zero {F : M2 n → ℂ} (hF : ContDiffOn ℂ ∞ F (Dom n)) {m : ℕ} (W : Fin (m + 1) → M2 n)
    (hW : ∀ i : Fin m, W 0 * W i.succ = 0) {x : M2 n} (hx : x ∈ Dom n) :
    iteratedFDeriv ℂ (m + 1) F x (fun i => x * W i) =
      fderiv ℂ (fun y => iteratedFDeriv ℂ m F y (fun i => y * W i.succ)) x (x * W 0) := by
  let Lm : M2 n →L[ℂ] (M2 n →L[ℂ] M2 n) :=
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℂ (M2 n)).toContinuousLinearMap
  have hcd : ContDiffAt ℂ ∞ F x := hF.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)
  have hΦ : DifferentiableAt ℂ (iteratedFDeriv ℂ m F) x :=
    hcd.differentiableAt_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m))
  have hfd := hΦ.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (g := fun _ : Fin m => fun y => Lm y) (fun _ => Lm.hasFDerivAt)
  have hfd2 := hfd.continuousMultilinear_apply_const (fun i => W i.succ)
  have eL : iteratedFDeriv ℂ (m + 1) F x (fun i => x * W i) =
      fderiv ℂ (iteratedFDeriv ℂ m F) x (x * W 0) (fun i => x * W i.succ) :=
    iteratedFDeriv_succ_apply_left _
  have e1 : fderiv ℂ (fun y => iteratedFDeriv ℂ m F y (fun i => y * W i.succ)) x (x * W 0) =
      fderiv ℂ (iteratedFDeriv ℂ m F) x (x * W 0) (fun i => x * W i.succ) +
        (iteratedFDeriv ℂ m F x).fderivCompContinuousLinearMap (fun _ => Lm x) (fun _ => Lm (x * W 0))
          (fun i => W i.succ) :=
    congrArg (fun T => T (x * W 0)) hfd2.fderiv
  have hS : (iteratedFDeriv ℂ m F x).fderivCompContinuousLinearMap (fun _ => Lm x) (fun _ => Lm (x * W 0))
      (fun i => W i.succ) = 0 := by
    refine (ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply (iteratedFDeriv ℂ m F x)
      (fun _ => Lm x) (fun _ => Lm (x * W 0)) (fun i => W i.succ)).trans ?_
    apply Finset.sum_eq_zero
    intro i _
    apply ContinuousMultilinearMap.map_coord_zero _ i
    refine (congrArg (fun f : M2 n →L[ℂ] M2 n => f (W i.succ))
      (Function.update_self i (Lm (x * W 0)) (fun _ : Fin m => Lm x))).trans ?_
    show x * W 0 * W i.succ = 0
    rw [Matrix.mul_assoc, hW i, Matrix.mul_zero]
  rw [eL, e1, hS, add_zero]

private theorem contDiffOn_foldr_fderiv_mul (l : List (M2 n)) {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) :
    ContDiffOn ℂ ∞ (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G) (Dom n) := by
  induction l with
  | nil => exact hG
  | cons a l ih => exact contDiffOn_fderiv_apply_mul_right ih a

private theorem foldr_fderiv_mul_left_eq_of_equivariant (l : List (M2 n)) {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) {P : M2 n}
    (hP : InP P) (c : ℂ) (h : ∀ x ∈ Dom n, G (P * x) = c * G x) :
    ∀ x ∈ Dom n, l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G (P * x) =
      c * l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G x := by
  induction l with
  | nil => exact h
  | cons a l ih => exact fderiv_apply_mul_equivariant_of_equivariant (contDiffOn_foldr_fderiv_mul l hG) hP c ih a

private theorem iteratedFDeriv_mul_eq_foldr_fderiv_of_mul_zero {F : M2 n → ℂ} (hF : ContDiffOn ℂ ∞ F (Dom n)) :
    ∀ (m : ℕ) (W : Fin m → M2 n), (∀ i j, W i * W j = 0) → ∀ x ∈ Dom n,
      iteratedFDeriv ℂ m F x (fun i => x * W i) =
        (List.ofFn W).foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) F x := by
  intro m
  induction m with
  | zero =>
    intro W _ x _
    simp [iteratedFDeriv_zero_apply]
  | succ m ih =>
    intro W hW x hx
    rw [iteratedFDeriv_succ_mul_eq_fderiv_of_mul_zero hF W (fun i => hW 0 i.succ) hx, List.ofFn_succ, List.foldr_cons]
    exact eqOn_fderiv_apply_mul_of_eqOn (fun y hy => ih (fun i => W i.succ) (fun i j => hW _ _) y hy) (W 0) hx

private theorem foldr_fderiv_comm_fderiv_of_mul_zero (l : List (M2 n)) {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) (Z : M2 n)
    (hZ : ∀ a ∈ l, Z * a = 0 ∧ a * Z = 0) :
    Set.EqOn (fun x => fderiv ℂ (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G) x (x * Z))
      (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) (fun x => fderiv ℂ G x (x * Z))) (Dom n) := by
  induction l with
  | nil => intro x _; rfl
  | cons a l ih =>
    intro x hx
    have ha : Z * a = 0 ∧ a * Z = 0 := hZ a (by simp)
    have h1 := fderiv_fderiv_mul_comm_of_mul_zero (contDiffOn_foldr_fderiv_mul l hG) ha.1 ha.2 x hx
    have h2 := eqOn_fderiv_apply_mul_of_eqOn (ih (fun b hb => hZ b (List.mem_cons_of_mem a hb))) a hx
    exact h1.trans h2

private theorem foldr_fderiv_reverse_eqOn_of_mul_zero (l : List (M2 n)) :
    ∀ {G : M2 n → ℂ}, ContDiffOn ℂ ∞ G (Dom n) → (∀ a ∈ l, ∀ b ∈ l, a * b = 0) →
      Set.EqOn (l.reverse.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G)
        (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G) (Dom n) := by
  induction l with
  | nil => intro G _ _ x _; rfl
  | cons a l ih =>
    intro G hG hl x hx
    have e1 := ih (contDiffOn_fderiv_apply_mul_right hG a)
      (fun b hb c hc => hl b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc)) hx
    have e2 := foldr_fderiv_comm_fderiv_of_mul_zero l hG a
      (fun b hb => ⟨hl a (by simp) b (by simp [hb]), hl b (by simp [hb]) a (by simp)⟩) hx
    rw [List.reverse_cons, List.foldr_append]
    exact e1.trans e2.symm

private theorem transpose_lemma_14 (hI : InfInv) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg]
    [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n)
    (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (χ1 χ2 : M2 n → ℂ)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (l : List (M2 n)) (hl : ∀ a ∈ l, ∀ b ∈ l, a * b = 0) (G1 : M2 n → ℂ) (hG1 : ContDiffOn ℂ ∞ G1 (Dom n))
    (h1 : ∀ P x, InP P → x ∈ Dom n → G1 (P * x) = χ1 P * G1 x) :
    ∀ (G2 : M2 n → ℂ), ContDiffOn ℂ ∞ G2 (Dom n) → (∀ P x, InP P → x ∈ Dom n → G2 (P * x) = χ2 P * G2 x) →
      ∫ k, l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G1 (ι k) * G2 (ι k) ∂μ =
        (-1) ^ l.length * ∫ k, G1 (ι k) * l.reverse.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G2 (ι k) ∂μ := by
  have hin : ∀ k, ι k ∈ Dom n := fun k => mem_dom_of_inG ((hK _).mpr ⟨k, rfl⟩).1
  have hint : ∀ H K : M2 n → ℂ, ContDiffOn ℂ ∞ H (Dom n) → ContDiffOn ℂ ∞ K (Dom n) →
      Integrable (fun k => H (ι k) * K (ι k)) μ := by
    intro H K hH hK'
    have c1 : Continuous (fun k => H (ι k)) := hH.continuousOn.comp_continuous hι hin
    have c2 : Continuous (fun k => K (ι k)) := hK'.continuousOn.comp_continuous hι hin
    exact (c1.mul c2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  induction l with
  | nil =>
    intro G2 _ _
    simp
  | cons a l ih =>
    intro G2 hG2 h2
    have hl' : ∀ b ∈ l, ∀ c ∈ l, b * c = 0 :=
      fun b hb c hc => hl b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc)
    set H1 := l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G1 with hH1def
    have hH1 : ContDiffOn ℂ ∞ H1 (Dom n) := contDiffOn_foldr_fderiv_mul l hG1
    have hH1e : ∀ P x, InP P → x ∈ Dom n → H1 (P * x) = χ1 P * H1 x :=
      fun P x hP hx => foldr_fderiv_mul_left_eq_of_equivariant l hG1 hP (χ1 P) (fun y hy => h1 P y hP hy) x hx
    have hG2' : ContDiffOn ℂ ∞ (fun x => fderiv ℂ G2 x (x * a)) (Dom n) := contDiffOn_fderiv_apply_mul_right hG2 a
    have h2' : ∀ P x, InP P → x ∈ Dom n → fderiv ℂ G2 (P * x) (P * x * a) = χ2 P * fderiv ℂ G2 x (x * a) :=
      fun P x hP hx => fderiv_apply_mul_equivariant_of_equivariant hG2 hP (χ2 P) (fun y hy => h2 P y hP hy) a x hx
    have hinv := hI n H1 G2 (Dom n) isOpen_dom_analytic_determinants (fun x hx => mem_dom_of_inG hx) hH1 hG2
      (by
        intro p x hp hp21 hx
        have hP : InP p := ⟨hp, hp21⟩
        have hxD := mem_dom_of_inG hx
        rw [hH1e p x hP hxD, h2 p x hP hxD, ← h12 p hP]
        ring) Kg μ ι hι hK a
    rw [integral_add (hint _ _ (contDiffOn_fderiv_apply_mul_right hH1 a) hG2) (hint _ _ hH1 hG2')] at hinv
    have eA : ∫ k, (fun x => fderiv ℂ H1 x (x * a)) (ι k) * G2 (ι k) ∂μ =
        -∫ k, H1 (ι k) * (fun x => fderiv ℂ G2 x (x * a)) (ι k) ∂μ := eq_neg_of_add_eq_zero_left hinv
    have eB := ih hl' (fun x => fderiv ℂ G2 x (x * a)) hG2' h2'
    simp only [List.foldr_cons, List.reverse_cons, List.foldr_append, List.foldr_nil, List.length_cons]
    rw [eA, eB, pow_succ]
    ring

theorem transpose (hI : InfInv) (F1 F2 : M2 n → ℂ) (χ1 χ2 : M2 n → ℂ) (hF1 : ContDiffOn ℂ ∞ F1 (Dom n))
    (hF2 : ContDiffOn ℂ ∞ F2 (Dom n)) (h1 : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = χ1 P * F1 x)
    (h2 : ∀ P x, InP P → x ∈ Dom n → F2 (P * x) = χ2 P * F2 x)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (N : ℕ) (W : Fin N → M2 n) (hW : ∀ a b, W a * W b = 0) :
    ∫ k, iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W i) * F2 (ι k) ∂μ =
      (-1) ^ N * ∫ k, F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W i) ∂μ := by
  have hin : ∀ k, ι k ∈ Dom n := fun k => mem_dom_of_inG ((hK _).mpr ⟨k, rfl⟩).1
  have hl : ∀ a ∈ List.ofFn W, ∀ b ∈ List.ofFn W, a * b = 0 := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    exact hW i j
  have eA : ∀ k, iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W i) =
      (List.ofFn W).foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) F1 (ι k) :=
    fun k => iteratedFDeriv_mul_eq_foldr_fderiv_of_mul_zero hF1 N W hW (ι k) (hin k)
  have eB : ∀ k, iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W i) =
      (List.ofFn W).reverse.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) F2 (ι k) :=
    fun k => (iteratedFDeriv_mul_eq_foldr_fderiv_of_mul_zero hF2 N W hW (ι k) (hin k)).trans (foldr_fderiv_reverse_eqOn_of_mul_zero (List.ofFn W) hF2 hl (hin k)).symm
  simp_rw [eA, eB]
  have key := transpose_lemma_14 hI Kg μ ι hι hK χ1 χ2 h12 (List.ofFn W) hl F1 hF1 h1 F2 hF2 h2
  rw [List.length_ofFn] at key
  exact key

theorem iteratedFDeriv_left_mul (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (M x : M2 n)
    (hx : M * x ∈ U) (N : ℕ) (v : Fin N → M2 n) :
    iteratedFDeriv ℂ N (fun y => F (M * y)) x v = iteratedFDeriv ℂ N F (M * x) (fun i => M * v i) := by
  let g : M2 n →L[ℂ] M2 n := (LinearMap.mulLeft ℂ M).toContinuousLinearMap
  have hpre : IsOpen (g ⁻¹' U) := hU.preimage g.continuous
  have hx' : x ∈ g ⁻¹' U := hx
  have key := g.iteratedFDerivWithin_comp_right hF hU.uniqueDiffOn hpre.uniqueDiffOn hx' (i := N)
    (by exact_mod_cast le_top)
  have e1 : iteratedFDerivWithin ℂ N (F ∘ g) (g ⁻¹' U) x = iteratedFDeriv ℂ N (F ∘ g) x :=
    iteratedFDerivWithin_of_isOpen N hpre hx'
  have e2 : iteratedFDerivWithin ℂ N F U (g x) = iteratedFDeriv ℂ N F (g x) :=
    iteratedFDerivWithin_of_isOpen N hU hx
  have key2 : iteratedFDeriv ℂ N (F ∘ g) x =
      (iteratedFDeriv ℂ N F (g x)).compContinuousLinearMap fun _ => g := by
    rw [← e1, ← e2]
    exact key
  have hfg : (fun y => F (M * y)) = F ∘ g := rfl
  rw [hfg, key2]
  rfl

theorem continuousOn_iteratedFDeriv_translate (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (Kg : Type) [TopologicalSpace Kg] (ι : Kg → M2 n) (hι : Continuous ι) (c : Kg → ℂ) (hc : Continuous c) (N : ℕ) :
    ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N (fun x => F (ι y.1 * x) * c y.1) y.2)
      (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}) := by
  let Lm : M2 n →L[ℂ] (M2 n →L[ℂ] M2 n) :=
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℂ (M2 n)).toContinuousLinearMap
  have key : ∀ y ∈ Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U},
      iteratedFDeriv ℂ N (fun x => F (ι y.1 * x) * c y.1) y.2 =
        c y.1 • ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
          (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ (fun _ => Lm (ι y.1))
          (iteratedFDeriv ℂ N F (ι y.1 * y.2)) := by
    rintro ⟨k, x⟩ ⟨-, hx⟩
    have hx' : ι k * x ∈ U := hx k
    have hcd : ContDiffAt ℂ N (fun z => F (ι k * z)) x := by
      have h1 : ContDiffAt ℂ ∞ F (Lm (ι k) x) := hF.contDiffAt (hU.mem_nhds hx')
      exact (h1.comp x (Lm (ι k)).contDiff.contDiffAt).of_le (by exact_mod_cast le_top)
    have hfun : (fun z => F (ι k * z) * c k) = c k • (fun z => F (ι k * z)) := by
      funext z
      simp [mul_comm]
    simp only
    rw [hfun, iteratedFDeriv_const_smul_apply hcd]
    congr 1
    ext v
    rw [iteratedFDeriv_left_mul F U hU hF (ι k) x hx' N v]
    rfl
  refine ContinuousOn.congr ?_ key
  refine ContinuousOn.smul (hc.comp continuous_fst).continuousOn ?_
  have hD : ContinuousOn (iteratedFDeriv ℂ N F) U := by
    have := hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) hU.uniqueDiffOn
    exact this.congr (fun y hy => (iteratedFDerivWithin_of_isOpen N hU hy).symm)
  have h1 : ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N F (ι y.1 * y.2))
      (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}) :=
    hD.comp ((hι.comp continuous_fst).mul continuous_snd).continuousOn (fun y hy => hy.2 y.1)
  have h2 : Continuous (fun y : Kg × M2 n =>
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ (fun _ => Lm (ι y.1))) :=
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ).cont.comp
      (continuous_pi fun _ => Lm.continuous.comp (hι.comp continuous_fst))
  exact h2.continuousOn.clm_apply h1

end PositivityTheory.Rg.Sw.LVs
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem rising_product_ne_zero (a : ℤ) (m : ℕ) (h : ∀ i : ℕ, i < m → (i : ℤ) + a ≠ 0) :
    ∏ i ∈ Finset.range m, ((a : ℂ) + (i : ℂ)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi h0
  apply h i (Finset.mem_range.1 hi)
  have : (((i : ℤ) + a : ℤ) : ℂ) = 0 := by push_cast; linear_combination h0
  exact_mod_cast this

theorem herm_isHermitian (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  simp only [herm, Matrix.conjTranspose_apply]
  apply Complex.ext <;> simp <;> ring

theorem inG_nU_herm (x : Fin n → Fin n → ℝ) : InG (nU (herm x)) := by
  have hH := herm_isHermitian x
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hH]

theorem fubini_step (p q : ℤ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (a b : M2 n) (ha : InG a) (hb : InG b) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    (hψ : IsSingTest ψ) :
    ∫ k, (∫ x, f0 p q (ι k * a * nU (herm x) * b) * ψ x) * (f0 p q (ι k))⁻¹ ∂μ =
      ∫ x, (∫ k, f0 p q (ι k * (a * nU (herm x) * b)) * (f0 p q (ι k))⁻¹ ∂μ) * ψ x := by
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hU0 : ∀ g : M2 n, InG g → g ∈ {x : M2 n | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} := fun g hg =>
    ⟨(gset_sub_dom hg).2.1, (gset_sub_dom hg).2.2.1⟩
  have hf0c : ContinuousOn (f0 (n := n) p q) {x : M2 n | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} :=
    (contDiffOn_scalar_section p q).continuousOn
  have hf0ne : ∀ k, f0 p q (ι k) ≠ 0 := fun k h => by
    have := scalar_section_mul_conjugate_section ((hK (ι k)).2 ⟨k, rfl⟩) p q; rw [h, zero_mul] at this; exact zero_ne_one this
  have hc : Continuous fun k => (f0 p q (ι k))⁻¹ :=
    (hf0c.comp_continuous hι (fun k => hU0 _ (hιG k))).inv₀ hf0ne
  have hherm : Continuous (herm (n := n)) := by
    unfold herm; fun_prop
  have hnU : Continuous fun x : Fin n → Fin n → ℝ => nU (herm x) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hmap : Continuous fun z : Kg × (Fin n → Fin n → ℝ) => ι z.1 * a * nU (herm z.2) * b :=
    (((hι.comp continuous_fst).mul continuous_const).mul (hnU.comp continuous_snd)).mul continuous_const
  set F : Kg × (Fin n → Fin n → ℝ) → ℂ := fun z => f0 p q (ι z.1 * a * nU (herm z.2) * b) * ψ z.2 *
    (f0 p q (ι z.1))⁻¹ with hFdef
  have hFc : Continuous F :=
    ((hf0c.comp_continuous hmap (fun z => hU0 _ (inG_mul (inG_mul (inG_mul (hιG z.1) ha) (inG_nU_herm z.2)) hb))).mul
      (hψ.1.comp continuous_snd)).mul (hc.comp continuous_fst)
  have hFs : HasCompactSupport F := by
    refine IsCompact.of_isClosed_subset (isCompact_univ.prod hψ.2.1) (isClosed_tsupport F) ?_
    refine closure_minimal (fun z hz => ⟨Set.mem_univ _, subset_tsupport ψ ?_⟩)
      (isClosed_univ.prod (isClosed_tsupport ψ))
    intro h0; apply hz; simp [hFdef, h0]
  have hFi : Integrable F (μ.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  have e1 : ∀ k, (∫ x, f0 p q (ι k * a * nU (herm x) * b) * ψ x) * (f0 p q (ι k))⁻¹ = ∫ x, F (k, x) := by
    intro k; rw [← integral_mul_const]
  have e2 : ∀ x, (∫ k, f0 p q (ι k * (a * nU (herm x) * b)) * (f0 p q (ι k))⁻¹ ∂μ) * ψ x = ∫ k, F (k, x) ∂μ := by
    intro x; rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hFdef, mul_assoc]; ring
  simp_rw [e1, e2]
  exact integral_integral_swap (f := fun k x => F (k, x)) hFi

theorem embOn_add (s : Finset (Fin n)) (T T' : Matrix s s ℂ) : embOn s (T + T') = embOn s T + embOn s T' := by
  ext a b; simp only [embOn, Matrix.add_apply]; split_ifs <;> simp

theorem embOn_smul (s : Finset (Fin n)) (c : ℂ) (T : Matrix s s ℂ) : embOn s (c • T) = c • embOn s T := by
  ext a b; simp only [embOn, Matrix.smul_apply]; split_ifs <;> simp

theorem WD_add (Q Q' R R' : Matrix (Fin n) (Fin n) ℂ) : WD (Q + Q') (R + R') = WD Q R + WD Q' R' := by
  have : fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (Q + Q') (R + R') 0 = fromBlocks 0 Q R 0 + fromBlocks 0 Q' R' 0 := by
    rw [Matrix.fromBlocks_add, add_zero]
  simp only [WD, this, Matrix.mul_add, Matrix.add_mul]

theorem WD_smul (c : ℂ) (Q R : Matrix (Fin n) (Fin n) ℂ) : WD (c • Q) (c • R) = c • WD Q R := by
  have : fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • Q) (c • R) 0 = c • fromBlocks 0 Q R 0 := by
    rw [Matrix.fromBlocks_smul, smul_zero]
  simp only [WD, this, Matrix.mul_smul, Matrix.smul_mul]

theorem WD_split (Q R : Matrix (Fin n) (Fin n) ℂ) : WD Q R = WD Q 0 + WD 0 R := by
  rw [← WD_add]; simp

def LQ (s : Finset (Fin n)) (x : M2 n) : Matrix s s ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => x * WD (embOn s T) 0
      map_add' := fun T T' => by
        have h := WD_add (embOn s T) (embOn s T') (0 : Matrix (Fin n) (Fin n) ℂ) 0
        rw [add_zero] at h
        rw [embOn_add, h, Matrix.mul_add]
      map_smul' := fun c T => by
        have h := WD_smul c (embOn s T) (0 : Matrix (Fin n) (Fin n) ℂ)
        rw [smul_zero] at h
        simp only [RingHom.id_apply]
        rw [embOn_smul, h, Matrix.mul_smul] }

def LR (s : Finset (Fin n)) (x : M2 n) : Matrix s s ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => x * WD 0 (embOn s T)
      map_add' := fun T T' => by
        have h := WD_add (0 : Matrix (Fin n) (Fin n) ℂ) 0 (embOn s T) (embOn s T')
        rw [add_zero] at h
        rw [embOn_add, h, Matrix.mul_add]
      map_smul' := fun c T => by
        have h := WD_smul c (0 : Matrix (Fin n) (Fin n) ℂ) (embOn s T)
        rw [smul_zero] at h
        simp only [RingHom.id_apply]
        rw [embOn_smul, h, Matrix.mul_smul] }

theorem LQ_apply (s : Finset (Fin n)) (x : M2 n) (T : Matrix s s ℂ) : LQ s x T = x * WD (embOn s T) 0 := rfl

theorem LR_apply (s : Finset (Fin n)) (x : M2 n) (T : Matrix s s ℂ) : LR s x T = x * WD 0 (embOn s T) := rfl

theorem mul_mX (x : M2 n) (Q R : Matrix (Fin n) (Fin n) ℂ) : x * mX 1 Q R 1 = x + x * WD Q 0 + x * WD 0 R := by
  rw [mX_eq, Matrix.mul_add, Matrix.mul_one, WD_split, Matrix.mul_add, add_assoc]

theorem fin_append_mul {a b : ℕ} (M : M2 n) (u : Fin a → M2 n) (v : Fin b → M2 n) :
    (fun i => M * Fin.append u v i) = Fin.append (fun i => M * u i) (fun i => M * v i) := by
  funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

theorem contDiff_mulLeft (M : M2 n) : ContDiff ℂ ∞ (fun x : M2 n => M * x) :=
  (LinearMap.mulLeft ℂ M).toContinuousLinearMap.contDiff

theorem contDiff_nU_sandwich (a b : M2 n) : ContDiff ℂ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun H => a * fromBlocks 0 H 0 0 * b
      map_add' := fun H H' => by
        have : (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (H + H') 0 0 : M2 n) = fromBlocks 0 H 0 0 + fromBlocks 0 H' 0 0 := by
          rw [Matrix.fromBlocks_add]; simp
        rw [this, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c H => by
        have : (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • H) 0 0 : M2 n) = c • fromBlocks 0 H 0 0 := by
          rw [Matrix.fromBlocks_smul]; simp
        simp only [RingHom.id_apply]
        rw [this, Matrix.mul_smul, Matrix.smul_mul] }
  have h : (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) = fun H => a * b + L.toContinuousLinearMap H := by
    funext H
    have : nU H = 1 + (fromBlocks 0 H 0 0 : M2 n) := by
      rw [nU, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]; simp
    simp only [L, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  rw [h]
  exact contDiff_const.add L.toContinuousLinearMap.contDiff

theorem iteratedFDeriv_mul_const_of (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (c : ℂ)
    (x : M2 n) (hx : x ∈ U) (N : ℕ) (v : Fin N → M2 n) :
    iteratedFDeriv ℂ N (fun y => F y * c) x v = iteratedFDeriv ℂ N F x v * c := by
  have hFx : ContDiffAt ℂ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
  have h := ContinuousLinearMap.iteratedFDeriv_comp_left ((ContinuousLinearMap.mul ℂ ℂ).flip c) hFx
    (i := N) (by exact_mod_cast le_top)
  have e : (fun y => F y * c) = (ContinuousLinearMap.mul ℂ ℂ).flip c ∘ F := by funext y; rfl
  rw [e, h]; rfl

theorem integrable_of_continuous_K {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasureOnCompacts μ] {f : Kg → ℂ} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f) (Set.subset_univ _))

theorem detD_detD_mul_const {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (x₀ : M2 n) (hx : x₀ ∈ U)
    (LA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : Matrix ιB ιB ℂ →L[ℂ] M2 n) (c : ℂ) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S) * c)) =
      detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) * c := by
  rw [detD_detD_comp (fun y => F y * c) U hU (hF.mul contDiffOn_const) x₀ hx LA LB,
    detD_detD_comp F U hU hF x₀ hx LA LB, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [iteratedFDeriv_mul_const_of F U hU hF c x₀ hx]; ring

end PositivityTheory.Rg.Sw.LVs
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem integrable_iteratedFDeriv_translate (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasureOnCompacts μ] (ι : Kg → M2 n) (hι : Continuous ι) (c : Kg → ℂ) (hc : Continuous c)
    (N : ℕ) (x : M2 n) (hx : ∀ k, ι k * x ∈ U) (w : Fin N → M2 n) :
    Integrable (fun k => iteratedFDeriv ℂ N (fun y => F (ι k * y) * c k) x w) μ := by
  have h := continuousOn_iteratedFDeriv_translate F U hU hF Kg ι hι c hc N
  have hg : Continuous (fun k : Kg => (k, x)) := continuous_id.prodMk continuous_const
  have hm : ∀ k, (k, x) ∈ (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U} : Set (Kg × M2 n)) :=
    fun k => ⟨Set.mem_univ _, hx⟩
  have h2 : Continuous (fun k : Kg => iteratedFDeriv ℂ N (fun y => F (ι k * y) * c k) x) :=
    h.comp_continuous hg hm
  exact integrable_of_continuous_K μ ((continuous_eval_const w).comp h2)

theorem spherical_detD (hHI : HolInt) (F : M2 n → ℂ) (hF : ContDiffOn ℂ ∞ F (Dom n))
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ] (ι : Kg → M2 n) (hι : Continuous ι)
    (c : Kg → ℂ) (hc : Continuous c)
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (LA : M2 n → Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : M2 n → Matrix ιB ιB ℂ →L[ℂ] M2 n)
    (hLA : ∀ M x T, LA (M * x) T = M * LA x T) (hLB : ∀ M x S, LB (M * x) S = M * LB x S)
    (g : M2 n) (hg : ∀ k, ι k * g ∈ Dom n) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ)) =
      ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k ∂μ := by
  classical
  set Ω : Set (M2 n) := {x | ∀ k, ι k * x ∈ Dom n} with hΩ
  have hΩo : IsOpen Ω := isOpen_domK Kg ι hι
  have hsm : ∀ k, ContDiffOn ℂ ∞ (fun x => F (ι k * x) * c k) Ω := fun k =>
    (hF.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ Ω) => hx k)).mul contDiffOn_const
  have hH := hHI n Kg μ Ω (fun k x => F (ι k * x) * c k) hΩo
    (fun N => continuousOn_iteratedFDeriv_translate F (Dom n) isOpen_dom hF Kg ι hι c hc N) hsm
  have hgΩ : g ∈ Ω := hg
  have hAv : ContDiffOn ℂ ∞ (fun x => ∫ k, F (ι k * x) * c k ∂μ) Ω := hH.1
  have key : ∀ (N : ℕ) (v : Fin N → M2 n), iteratedFDeriv ℂ N (fun x => ∫ k, F (ι k * x) * c k ∂μ) g v =
      ∫ k, iteratedFDeriv ℂ N (fun x => F (ι k * x) * c k) g v ∂μ := fun N v => hH.2 N g v hgΩ
  have e0 : (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ))
      = fun T => detD (fun S => (fun x => ∫ k, F (ι k * x) * c k ∂μ) (g + LA g T + LB g S)) := rfl
  have hFc : ∀ k, ContDiffOn ℂ ∞ (fun y => F y * c k) (Dom n) := fun k => hF.mul contDiffOn_const
  have hk : ∀ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
      F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun x => F (ι k * x) * c k) g
          (Fin.append (fun i => LA g (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB g (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    intro k
    rw [← detD_detD_mul_const F (Dom n) isOpen_dom hF (ι k * g) (hg k) (LA (ι k * g)) (LB (ι k * g)) (c k),
      detD_detD_comp (fun y => F y * c k) (Dom n) isOpen_dom (hFc k) (ι k * g) (hg k) _ _]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    congr 1
    rw [iteratedFDeriv_left_mul (fun y => F y * c k) (Dom n) isOpen_dom (hFc k) (ι k) g (hg k), fin_append_mul]
    simp only [hLA, hLB]
  have hint : ∀ (σ : Equiv.Perm ιA) (τ : Equiv.Perm ιB), Integrable (fun k =>
      iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun x => F (ι k * x) * c k) g
          (Fin.append (fun i => LA g (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB g (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1)))) μ :=
    fun σ τ => integrable_iteratedFDeriv_translate F (Dom n) isOpen_dom hF μ ι hι c hc _ g hg _
  rw [e0, detD_detD_comp _ Ω hΩo hAv g hgΩ (LA g) (LB g), integral_congr_ae (Filter.Eventually.of_forall hk)]
  simp only [key]
  symm
  rw [integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint σ τ).const_mul _))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finset_sum _ (fun τ _ => (hint σ τ).const_mul _)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul]

theorem transpose_detD (hI : InfInv) (F1 F2 : M2 n → ℂ) (χ1 χ2 : M2 n → ℂ) (hF1 : ContDiffOn ℂ ∞ F1 (Dom n))
    (hF2 : ContDiffOn ℂ ∞ F2 (Dom n)) (h1 : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = χ1 P * F1 x)
    (h2 : ∀ P x, InP P → x ∈ Dom n → F2 (P * x) = χ2 P * F2 x)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (WA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (WB : Matrix ιB ιB ℂ →L[ℂ] M2 n)
    (hW : ∀ (T T' : Matrix ιA ιA ℂ) (S S' : Matrix ιB ιB ℂ), (WA T + WB S) * (WA T' + WB S') = 0) :
    ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F1 (ι k + ι k * WA T + ι k * WB S))) * F2 (ι k) ∂μ =
      (-1) ^ (Fintype.card ιA + Fintype.card ιB) * ∫ k, F1 (ι k) * detD (fun T : Matrix ιA ιA ℂ =>
        detD (fun S : Matrix ιB ιB ℂ => F2 (ι k + ι k * WA T + ι k * WB S))) ∂μ := by
  classical
  have hιK : ∀ k, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hιDom : ∀ k, ι k ∈ Dom n := fun k => gset_sub_dom (hιK k).1
  set N := Fintype.card ιA + Fintype.card ιB with hN
  let W : Equiv.Perm ιA → Equiv.Perm ιB → Fin N → M2 n := fun σ τ =>
    Fin.append (fun i => WA (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
      (fun i => WB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))
  have hWW : ∀ σ τ a b, W σ τ a * W σ τ b = 0 := by
    intro σ τ a b
    have hAA : ∀ T T' : Matrix ιA ιA ℂ, WA T * WA T' = 0 := fun T T' => by
      simpa only [map_zero, add_zero] using hW T T' 0 0
    have hAB : ∀ (T : Matrix ιA ιA ℂ) (S' : Matrix ιB ιB ℂ), WA T * WB S' = 0 := fun T S' => by
      simpa only [map_zero, add_zero, zero_add] using hW T 0 0 S'
    have hBA : ∀ (S : Matrix ιB ιB ℂ) (T' : Matrix ιA ιA ℂ), WB S * WA T' = 0 := fun S T' => by
      simpa only [map_zero, add_zero, zero_add] using hW 0 T' S 0
    have hBB : ∀ S S' : Matrix ιB ιB ℂ, WB S * WB S' = 0 := fun S S' => by
      simpa only [map_zero, zero_add] using hW 0 0 S S'
    refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;> refine Fin.addCases (fun i' => ?_) (fun i' => ?_) b <;>
      simp only [W, Fin.append_left, Fin.append_right]
    · exact hAA _ _
    · exact hAB _ _
    · exact hBA _ _
    · exact hBB _ _
  have expand : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ k,
      detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (ι k + ι k * WA T + ι k * WB S))) =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ N F (ι k) (fun i => ι k * W σ τ i) := by
    intro F hF k
    have e := detD_detD_comp F (Dom n) isOpen_dom hF (ι k) (hιDom k)
      ((LinearMap.mulLeft ℂ (ι k)).toContinuousLinearMap.comp WA) ((LinearMap.mulLeft ℂ (ι k)).toContinuousLinearMap.comp WB)
    refine e.trans (Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_)
    congr 2
    rw [fin_append_mul]
    rfl
  have hcontD : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ σ τ,
      Continuous (fun k => iteratedFDeriv ℂ N F (ι k) (fun i => ι k * W σ τ i)) := by
    intro F hF σ τ
    have h1 : ContinuousOn (iteratedFDeriv ℂ N F) (Dom n) :=
      (hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) isOpen_dom.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen N isOpen_dom hx).symm)
    have h2 : Continuous (fun k => iteratedFDeriv ℂ N F (ι k)) := h1.comp_continuous hι hιDom
    have h3 : Continuous (fun k => (fun i => ι k * W σ τ i : Fin N → M2 n)) :=
      continuous_pi fun i => hι.mul continuous_const
    exact h2.eval h3
  have hc1 : Continuous fun k => F1 (ι k) := hF1.continuousOn.comp_continuous hι hιDom
  have hc2 : Continuous fun k => F2 (ι k) := hF2.continuousOn.comp_continuous hι hιDom
  have hint1 : ∀ σ τ, Integrable (fun k => iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W σ τ i) * F2 (ι k)) μ :=
    fun σ τ => integrable_of_continuous_K μ ((hcontD F1 hF1 σ τ).mul hc2)
  have hint2 : ∀ σ τ, Integrable (fun k => F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W σ τ i)) μ :=
    fun σ τ => integrable_of_continuous_K μ (hc1.mul (hcontD F2 hF2 σ τ))
  have eL : (fun k => detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F1 (ι k + ι k * WA T + ι k * WB S))) * F2 (ι k)) =
      fun k => ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        (iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W σ τ i) * F2 (ι k)) := by
    funext k; rw [expand F1 hF1 k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have eR : (fun k => F1 (ι k) * detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F2 (ι k + ι k * WA T + ι k * WB S)))) =
      fun k => ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        (F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W σ τ i)) := by
    funext k; rw [expand F2 hF2 k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  rw [eL, eR, integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint1 σ τ).const_mul _)),
    integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint2 σ τ).const_mul _)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finset_sum _ (fun τ _ => (hint1 σ τ).const_mul _),
    integral_finset_sum _ (fun τ _ => (hint2 σ τ).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, integral_const_mul,
    transpose hI F1 F2 χ1 χ2 hF1 hF2 h1 h2 h12 Kg μ ι hι hK N (W σ τ) (hWW σ τ)]
  ring

end PositivityTheory.Rg.Sw.LVs
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inG_one {n : ℕ} : InG (1 : M2 n) := by simp [InG]

private theorem exists_split_avoiding_of_goodSig (n p q : ℕ) (h : GoodSig n p q) :
    ∃ j ≤ n, (∀ i < j, i ≠ q) ∧ (∀ i < n - j, i ≠ p) ∧ (∀ i < j, i + p ≠ n) ∧ (∀ i < n - j, i + q ≠ n) := by
  unfold GoodSig at h
  rcases h with h | h | h | h
  · exact ⟨min q n, min_le_right _ _, by omega, by omega, by omega, by omega⟩
  · exact ⟨n - min p n, Nat.sub_le _ _, by omega, by omega, by omega, by omega⟩
  · exact ⟨0, Nat.zero_le _, by omega, by omega, by omega, by omega⟩
  · exact ⟨n, le_refl _, by omega, by omega, by omega, by omega⟩

private theorem integral_minorOn_wM_ne_zero {n : ℕ} (j : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g) :
    ∫ k, minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ * (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k))) ∂μ ≠ 0 := by
  have hKk : ∀ k, InK (ι k) := fun k => (hK _).2 ⟨k, rfl⟩
  have hU : ∀ k, wM (ι k) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    intro k
    have h1 := first_cayley_block_unitary (hKk k)
    have h2 := second_cayley_block_unitary (hKk k)
    have hu1 : u1 (ι k) ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.2 h1
    have hu2 : u2 (ι k) ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff.2 h2
    have hi : (u2 (ι k))⁻¹ = star (u2 (ι k)) := Matrix.inv_eq_right_inv h2
    unfold wM
    rw [hi]
    exact mul_mem (Unitary.star_mem hu2) hu1
  set g : Kg → ℝ := fun k => Complex.normSq (minorOn (blkA j) (wM (ι k))) * Complex.normSq (minorOn (blkB j) (wM (ι k))) with hg
  have hpt : ∀ k, minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ * (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k))) = ((g k : ℝ) : ℂ) := by
    intro k
    rw [minorOn_inv_of_unitary (hU k), minorOn_inv_of_unitary (hU k)]
    simp only [hg, Complex.ofReal_mul, ← Complex.mul_conj, Complex.star_def]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal]
  have hw1 : wM (1 : M2 n) = 1 := by
    have h1 : (1 : M2 n) = Matrix.fromBlocks 1 0 0 1 := Matrix.fromBlocks_one.symm
    unfold wM u1 u2
    rw [h1, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
    simp
  have hm1 : ∀ s : Finset (Fin n), minorOn s (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    intro s
    unfold minorOn
    rw [Matrix.submatrix_one _ Subtype.val_injective]
    simp
  have hcw : Continuous fun k => wM (ι k) :=
    continuousOn_wM.comp_continuous hι (fun k => det_second_cayley_block_ne_zero (hKk k).1)
  have hgc : Continuous g := by
    rw [hg]
    exact ((Complex.continuous_normSq.comp ((continuous_minorOn _).comp hcw))).mul
      (Complex.continuous_normSq.comp ((continuous_minorOn _).comp hcw))
  have hpos : 0 < ∫ k, g k ∂μ := by
    refine hgc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (HasCompactSupport.of_compactSpace _) (fun k => ?_) ?_
    · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    · simp [hg, map_one, hw1, hm1]
  exact_mod_cast hpos.ne'

theorem lv_of (hC : Cayley) (hU : UAct) (hDj : DjSec) (hDp : DpDual) (hHI : HolInt) (hHZ : HolZero)
    (hSD : SingToDiff) (hTC : TopComp) (hII : InfInv) : LV := by
  intro n p q hsig Kg _ _ _ _ _ _ μ _ ι hι hK
  by_contra hne
  push_neg at hne
  obtain ⟨j, hjn, hj1, hj2, hj3, hj4⟩ := exists_split_avoiding_of_goodSig n p q hsig
  have hC : ((∏ i ∈ Finset.range j, (-((q:ℤ):ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (-((p:ℤ):ℂ) + (i:ℂ))) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · have := rising_product_ne_zero (-(q:ℤ)) j (fun i hi => by have := hj1 i hi; omega)
      push_cast at this ⊢
      exact this
    · have := rising_product_ne_zero (-(p:ℤ)) (n - j) (fun i hi => by have := hj2 i hi; omega)
      push_cast at this ⊢
      exact this
  have hC' : ((∏ i ∈ Finset.range j, (((p:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (((q:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · have := rising_product_ne_zero ((p:ℤ) - n) j (fun i hi => by have := hj3 i hi; omega)
      push_cast at this ⊢
      exact this
    · have := rising_product_ne_zero ((q:ℤ) - n) (n - j) (fun i hi => by have := hj4 i hi; omega)
      push_cast at this ⊢
      exact this
  have hKk : ∀ k, InK (ι k) := fun k => (hK _).2 ⟨k, rfl⟩
  have hGk : ∀ k, InG (ι k) := fun k => (hKk k).1
  have hfv : ∀ k, (f0 (p:ℤ) (q:ℤ) (ι k))⁻¹ = fV (p:ℤ) (q:ℤ) (ι k) := fun k =>
    (eq_inv_of_mul_eq_one_right (scalar_section_mul_conjugate_section (hKk k) _ _)).symm
  set Ω : Set (M2 n) := {x : M2 n | ∀ k, ι k * x ∈ Dom n} with hΩdef
  have hΩ : IsOpen Ω := isOpen_domK Kg ι hι
  have hGΩ : ∀ g : M2 n, InG g → g ∈ Ω := fun g hg k => gset_sub_dom (inG_mul (hGk k) hg)
  have hf0 : ContDiffOn ℂ ∞ (f0 (p:ℤ) (q:ℤ)) (Dom n) :=
    (contDiffOn_scalar_section (n := n) _ _).mono (fun x hx => dom_sub x hx)
  have hcV : Continuous fun k => fV (p:ℤ) (q:ℤ) (ι k) :=
    cont_on_K _ (contDiffOn_fV _ _) Kg ι hι (fun k => gset_sub_dom (hGk k))
  have hk_cd : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ k : Kg,
      ContDiffOn ℂ ∞ (fun y => F (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k)) Ω := by
    intro F hF k
    exact (hF.comp (contDiff_mulLeft (ι k)).contDiffOn (fun y (hy : y ∈ Ω) => hy k)).mul contDiffOn_const
  set Φ : M2 n → ℂ := fun y => ∫ k, f0 (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ with hΦdef
  have hΦ : ContDiffOn ℂ ∞ Φ Ω :=
    (hHI n Kg μ Ω (fun k y => f0 (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k)) hΩ
      (cont_translate' _ _ isOpen_dom hf0 Kg ι hι _ hcV) (hk_cd _ hf0)).1
  have hD1 : ∀ a b : M2 n, InG a → InG b → detD (fun H : Matrix (Fin n) (Fin n) ℂ => Φ (a * nU H * b)) = 0 := by
    intro a b ha hb
    have hS : IsOpen ((fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) ⁻¹' Ω) :=
      hΩ.preimage (contDiff_nU_sandwich a b).continuous
    have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) ⁻¹' Ω := by
      have hn0 : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
        unfold nU
        exact Matrix.fromBlocks_one
      show a * nU 0 * b ∈ Ω
      rw [hn0, mul_one]
      exact hGΩ _ (inG_mul ha hb)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hS 0 h0
    refine hSD n _ r hr (hΦ.comp (contDiff_nU_sandwich a b).contDiffOn (fun H hH => hball hH)) ?_
    intro ψ hψ
    have h := hne ψ a b hψ ha hb
    rw [fubini_step (p:ℤ) (q:ℤ) Kg μ ι hι hK a b ha hb ψ hψ] at h
    simp only [hfv] at h
    exact h
  have hTop := hTC n j Φ Ω hΩ (fun g hg => hGΩ g hg) hΦ (by
      intro x P S _ _ hP hS
      show ∫ k, f0 (p:ℤ) (q:ℤ) (ι k * (x * mX (1 + P) 0 0 (1 + S))) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ
        = ∫ k, f0 (p:ℤ) (q:ℤ) (ι k * x) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ
      congr 1
      funext k
      rw [← mul_assoc, scalar_section_compact_block_invariant hU j _ _ _ P S hP hS]) hD1
  have hLQ : ∀ (M x : M2 n) (T : Matrix (blkA j) (blkA j) ℂ), LQ (blkA j) (M * x) T = M * LQ (blkA j) x T := by
    intro M x T
    rw [LQ_apply, LQ_apply, mul_assoc]
  have hLR : ∀ (M x : M2 n) (S : Matrix (blkB j) (blkB j) ℂ), LR (blkB j) (M * x) S = M * LR (blkB j) x S := by
    intro M x S
    rw [LR_apply, LR_apply, mul_assoc]
  have hm : ∀ (y : M2 n) (T : Matrix (blkA j) (blkA j) ℂ) (S : Matrix (blkB j) (blkB j) ℂ),
      y * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1 = y + LQ (blkA j) y T + LR (blkB j) y S := by
    intro y T S
    rw [mX_eq, WD_split, LQ_apply, LR_apply, mul_add, mul_add, mul_one, add_assoc]
  have key : ∀ y ∈ Dom n, (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      f0 (p:ℤ) (q:ℤ) (y + LQ (blkA j) y T + LR (blkB j) y S)) =
      ((∏ i ∈ Finset.range j, (-((q:ℤ):ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (-((p:ℤ):ℂ) + (i:ℂ))) * hF j p q y := by
    intro y hy
    have h := hDj n j p q y hjn (dom_sub y hy).1 (dom_sub y hy).2
    simp only [hm] at h
    rw [h]
    unfold hF
    ring
  set Ψ : M2 n → ℂ := fun y => ∫ k, hF j (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ with hΨdef
  have hΨ0 : ∀ g ∈ GSet n, Ψ g = 0 := by
    intro g hg
    have h := hTop g hg
    simp only [hm] at h
    rw [show (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
        Φ (g + LQ (blkA j) g T + LR (blkB j) g S)) = _ from
      spherical_detD hHI (f0 (p:ℤ) (q:ℤ)) hf0 μ ι hι _ hcV (LQ (blkA j)) (LR (blkB j)) hLQ hLR g
        (fun k => hGΩ g hg k)] at h
    have hc : (∫ k, (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
        f0 (p:ℤ) (q:ℤ) (ι k * g + LQ (blkA j) (ι k * g) T + LR (blkB j) (ι k * g) S)) * fV (p:ℤ) (q:ℤ) (ι k) ∂μ) =
        ∫ k, ((∏ i ∈ Finset.range j, (-((q:ℤ):ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (-((p:ℤ):ℂ) + (i:ℂ))) *
          (hF j p q (ι k * g) * fV (p:ℤ) (q:ℤ) (ι k)) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only
      rw [key _ (hGΩ g hg k)]
      ring
    rw [hc, integral_const_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hC
  have hΨc : ContDiffOn ℂ ∞ Ψ Ω :=
    (hHI n Kg μ Ω (fun k y => hF j (p:ℤ) (q:ℤ) (ι k * y) * fV (p:ℤ) (q:ℤ) (ι k)) hΩ
      (cont_translate' _ _ isOpen_dom (contDiffOn_hF j _ _) Kg ι hι _ hcV) (hk_cd _ (contDiffOn_hF j _ _))).1
  have hΨd : ∀ N : ℕ, iteratedFDeriv ℂ N Ψ 1 = 0 := fun N =>
    hHZ n Ω Ψ hΩ (fun g hg => hGΩ g hg) hΨc hΨ0 N 1 inG_one
  have hLR' : ∀ (M x : M2 n) (T : Matrix (blkA j) (blkA j) ℂ), LR (blkA j) (M * x) T = M * LR (blkA j) x T := by
    intro M x T
    rw [LR_apply, LR_apply, mul_assoc]
  have hLQ' : ∀ (M x : M2 n) (S : Matrix (blkB j) (blkB j) ℂ), LQ (blkB j) (M * x) S = M * LQ (blkB j) x S := by
    intro M x S
    rw [LQ_apply, LQ_apply, mul_assoc]
  have hsph := spherical_detD hHI (hF j (p:ℤ) (q:ℤ)) (contDiffOn_hF j _ _) μ ι hι _ hcV
    (LR (blkA j)) (LQ (blkB j)) hLR' hLQ' 1 (fun k => hGΩ 1 inG_one k)
  have hzero : (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      Ψ (1 + LR (blkA j) 1 T + LQ (blkB j) 1 S)) = 0 := by
    rw [detD_detD_comp Ψ Ω hΩ hΨc 1 (hGΩ 1 inG_one) (LR (blkA j) 1) (LQ (blkB j) 1)]
    simp [hΨd]
  rw [show (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      Ψ (1 + LR (blkA j) 1 T + LQ (blkB j) 1 S)) = _ from hsph] at hzero
  have htr := transpose_detD hII (hF j (p:ℤ) (q:ℤ)) (fV (p:ℤ) (q:ℤ)) (c1 (p:ℤ) (q:ℤ)) (c2 (p:ℤ) (q:ℤ))
    (contDiffOn_hF j _ _) (contDiffOn_fV _ _) (fun P x hP hx => hF_law j _ _ hP hx)
    (fun P x hP hx => fV_law _ _ hP hx) (fun P hP => modulus_characters_product _ _ hP) Kg μ ι hι hK
    (LR (blkA j) 1) (LQ (blkB j) 1) (by
      intro T T' S S'
      simp only [LR_apply, LQ_apply, one_mul]
      rw [add_comm (WD 0 _), add_comm (WD 0 _), ← WD_add, ← WD_add, add_zero, zero_add, add_zero, zero_add]
      exact WD_mul_WD_B_A j T S T' S')
  have e1 : ∀ (k : Kg) (T : Matrix (blkA j) (blkA j) ℂ) (S : Matrix (blkB j) (blkB j) ℂ),
      ι k * 1 + LR (blkA j) (ι k * 1) T + LQ (blkB j) (ι k * 1) S = ι k + ι k * LR (blkA j) 1 T + ι k * LQ (blkB j) 1 S := by
    intro k T S
    simp only [LR_apply, LQ_apply, mul_one, one_mul]
  simp only [e1] at hzero
  rw [htr] at hzero
  have e2 : ∀ (y : M2 n) (T : Matrix (blkA j) (blkA j) ℂ) (S : Matrix (blkB j) (blkB j) ℂ),
      y + y * LR (blkA j) 1 T + y * LQ (blkB j) 1 S = y * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1 := by
    intro y T S
    rw [mX_eq, WD_split, LR_apply, LQ_apply, one_mul, one_mul, mul_add, mul_add, mul_one, add_assoc, add_comm (y * WD 0 _)]
  simp only [e2] at hzero
  have hc : (∫ k, hF j (p:ℤ) (q:ℤ) (ι k) * (detD fun T : Matrix (blkA j) (blkA j) ℂ => detD fun S : Matrix (blkB j) (blkB j) ℂ =>
      fV (p:ℤ) (q:ℤ) (ι k * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1)) ∂μ) =
      ∫ k, ((∏ i ∈ Finset.range j, (((p:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (((q:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) *
        (minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ *
          (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k)))) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [hDp n j p q (ι k) hjn (hGk k)]
    have h1 := scalar_section_mul_conjugate_section (hKk k) (p:ℤ) (q:ℤ)
    unfold hF
    linear_combination ((∏ i ∈ Finset.range j, (((p:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) * ∏ i ∈ Finset.range (n - j), (((q:ℤ):ℂ) - (n:ℂ) + (i:ℂ))) *
        (minorOn (blkA j) (wM (ι k)) * minorOn (blkB j) (wM (ι k))⁻¹ *
          (minorOn (blkA j) (wM (ι k))⁻¹ * minorOn (blkB j) (wM (ι k)))) * h1
  rw [hc, integral_const_mul] at hzero
  exact integral_minorOn_wM_ne_zero j Kg μ ι hι hK
    ((mul_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_left (pow_ne_zero _ (by norm_num)))).resolve_left hC')

end PositivityTheory.Rg.Sw.LVs
end
end
