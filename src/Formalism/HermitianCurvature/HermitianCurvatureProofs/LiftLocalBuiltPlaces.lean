import Formalism.HermitianCurvature.HermitianCurvatureProofs.RatioBound

section
namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem toStd_append_blk (r : ℕ) (g : ℝ) (s : ℕ) (c : ℂ) : ∀ (h : C.LPt) (b : ℕ),
    D.toStd r g b (h ++ [(s, c)]) = D.toStd r g b h ++
      [(s, (((g / (2 * Real.pi)) ^ S6.nuBlock r ((b + D.ptSize h : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
        Complex.I ^ (s - 1) * c)]
  | [], b => by simp [D.toStd, D.ptSize]
  | (s', t) :: rest, b => by
    have ih := toStd_append_blk r g s c rest (b + s')
    simp only [List.cons_append, D.toStd, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc]

theorem slv_congr {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (i : ℕ) (hi : i ≤ r)
    (w : List C.Letter) {P P' : C.LPt} (e : P = P') (hP : D.ptSize P = i) (hP' : D.ptSize P' = i) :
    KB.slv T F i hi w P hP = KB.slv T F i hi w P' hP' := by
  subst e; rfl

theorem psd_shift {Y : Finset C.LPt} {k : C.LPt → C.LPt → ℂ} (blk : ℕ × ℂ)
    (hk : TB.PSDOn (Y.image fun h => h ++ [blk]) k) : TB.PSDOn Y fun p q => k (p ++ [blk]) (q ++ [blk]) := by
  have hinj : Set.InjOn (fun h : C.LPt => h ++ [blk]) Y := fun x _ y _ hxy => List.append_cancel_right hxy
  rw [PBA.psd_iff_qf] at hk ⊢
  obtain ⟨hh, hq⟩ := hk
  refine ⟨fun x hx y hy => hh _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy), fun c => ?_⟩
  have e : PBA.qf Y (fun p q => k (p ++ [blk]) (q ++ [blk])) c =
      PBA.qf (Y.image fun h => h ++ [blk]) k (fun z => c z.dropLast) := by
    unfold PBA.qf
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp
  rw [e]; exact hq _

section lam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def lamB (S : C.HidaSetting E Wp Wq) (b s : ℕ) : ℂ :=
  ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r (b : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1)

theorem stdS_blk (S : C.HidaSetting E Wp Wq) (b s : ℕ) (hb : 1 ≤ b) (H : C.LPt) (hH : D.ptSize H = b - 1) (t : ℂ) :
    stdS S (H ++ [(s, t)]) = stdS S H ++ [(s, lamB S b s * t)] := by
  unfold stdS lamB
  rw [toStd_append_blk, hH, show 1 + (b - 1) = b by omega]

theorem norm_lamB (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s : ℕ) :
    ‖lamB S b s‖ = ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r (b : ℤ) (s : ℤ) := by
  unfold lamB
  rw [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  exact zpow_nonneg (by positivity) _

theorem lamB_ne (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s : ℕ) : lamB S b s ≠ 0 := by
  intro h
  have := norm_lamB S hg b s
  rw [h, norm_zero] at this
  exact (zpow_pos (by positivity : (0 : ℝ) < (S.g : ℝ) / (2 * Real.pi)) _).ne this

end lam

section deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem uB_blk (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (b s : ℕ) (hb : 1 ≤ b) (H : C.LPt) (hH : D.ptSize H = b - 1) (t : ℂ)
    (hP : D.IsLocPt (H ++ [(s, t)]) j) :
    ∃ hX : D.IsLocPt (stdS S H ++ [(s, lamB S b s * t)]) j,
      uB S p F v ε j hj w (H ++ [(s, t)]) = (((√(nnS S (H ++ [(s, t)])) / bS S (H ++ [(s, t)]) : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S H ++ [(s, lamB S b s * t)]) hX.2 := by
  have hgpos := g_pos_of_built hB
  have e := stdS_blk S b s hb H hH t
  have hX : D.IsLocPt (stdS S H ++ [(s, lamB S b s * t)]) j := by
    rw [← e]; exact (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 j).2 hP
  refine ⟨hX, ?_⟩
  rw [uB_pos S p F v ε j hj w _ hP]
  congr 1
  exact slv_congr _ _ _ _ _ e _ _

theorem deg_uB_lift (hDL : KB.DegLift) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (b s : ℕ) (hb : 1 ≤ b) (a : List C.Letter) (K : ℕ)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ) (hinj : ∀ c, Function.Injective (grid c))
    (H H' : C.LPt) (hH : D.ptSize H = b - 1) (hH' : D.ptSize H' = b - 1) (t t' : ℂ) :
    ((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
        (p v).form j hj a (uB S p F v ε j hj a (H ++ [(s, t)])) (uB S p F v ε j hj a (H' ++ [(s, t')])) =
      ∑ n : Fin K → Fin (2 * (j - s) + s + 1), ((∏ c, F7.lagCo (grid c) (n c) : ℝ) : ℂ) *
        KB.pairJ ((p v).form j hj a) (List.ofFn fun c => grid c (n c))
          (uB S p F v ε j hj (KB.plusW (List.ofFn fun c => grid c (n c)) a) (H ++ [(s, t)]))
          (uB S p F v ε j hj (KB.minusW (List.ofFn fun c => grid c (n c)) a) (H' ++ [(s, t')])) := by
  by_cases hloc : D.IsLocPt (H ++ [(s, t)]) j ∧ D.IsLocPt (H' ++ [(s, t')]) j
  · obtain ⟨hP, hP'⟩ := hloc
    obtain ⟨hX, eX⟩ := uB_blk hB F v ε j hj a b s hb H hH t hP
    obtain ⟨hX', eX'⟩ := uB_blk hB F v ε j hj a b s hb H' hH' t' hP'
    have hdeg := hDL (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j s hj a (stdS S H) (stdS S H')
      (lamB S b s * t) (lamB S b s * t') hX hX' K grid (hF v ε hε) hinj
    rw [rr_eq_form (p v) (F v ε) j hj a _ _ hX hX'] at hdeg
    set Dh : ℂ := (((√(nnS S (H ++ [(s, t)])) / bS S (H ++ [(s, t)]) : ℝ) : ℂ)) with hDh
    set Dh' : ℂ := (((√(nnS S (H' ++ [(s, t')])) / bS S (H' ++ [(s, t')]) : ℝ) : ℂ)) with hDh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj a _ hX)
      (slv_nv (p v) (hF v ε hε) j hj a _ hX')
    rw [eX, eX', form_smul_l (p v) j hj a _ _ _ hs (nv_smul _ hs'), form_smul_r (p v) j hj a _ _ _ hs hs']
    have hL : ((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
        (Dh * (conj Dh' * (p v).form j hj a (KB.slv (p v).T (F v ε) j hj a _ hX.2)
          (KB.slv (p v).T (F v ε) j hj a _ hX'.2))) =
        Dh * conj Dh' * (((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
          (p v).form j hj a (KB.slv (p v).T (F v ε) j hj a _ hX.2) (KB.slv (p v).T (F v ε) j hj a _ hX'.2)) := by
      ring
    rw [hL, hdeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    set ys := List.ofFn fun c => grid c (n c) with hys
    obtain ⟨hXp, eXp⟩ := uB_blk hB F v ε j hj (KB.plusW ys a) b s hb H hH t hP
    obtain ⟨hXm, eXm⟩ := uB_blk hB F v ε j hj (KB.minusW ys a) b s hb H' hH' t' hP'
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj (KB.plusW ys a) _ hX)
      (slv_nv (p v) (hF v ε hε) j hj (KB.minusW ys a) _ hX')
    rw [eXp, eXm, pj_smul (p v) j hj a ys _ _ _ _ hp hm]
    ring
  · have h0 : ∀ w : List C.Letter, uB S p F v ε j hj w (H ++ [(s, t)]) = 0 ∨
        uB S p F v ε j hj w (H' ++ [(s, t')]) = 0 := by
      intro w
      by_cases hh : D.IsLocPt (H ++ [(s, t)]) j
      · exact Or.inr (uB_neg S p F v ε j hj w _ fun hh' => hloc ⟨hh, hh'⟩)
      · exact Or.inl (uB_neg S p F v ε j hj w _ hh)
    obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj a (H ++ [(s, t)]))
      (uB_nv hB F hF v ε hε j hj a (H' ++ [(s, t')]))
    have lhs0 : (p v).form j hj a (uB S p F v ε j hj a (H ++ [(s, t)])) (uB S p F v ε j hj a (H' ++ [(s, t')])) = 0 := by
      rcases h0 a with h0 | h0
      · rw [h0, form_zero_l (p v) j hj a _ hx']
      · rw [h0, form_zero_r (p v) j hj a _ hx]
    rw [lhs0, mul_zero]
    symm
    refine Finset.sum_eq_zero fun n _ => ?_
    set ys := List.ofFn fun c => grid c (n c) with hys
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (uB_nv hB F hF v ε hε j hj (KB.plusW ys a) (H ++ [(s, t)]))
      (uB_nv hB F hF v ε hε j hj (KB.minusW ys a) (H' ++ [(s, t')]))
    by_cases hh : D.IsLocPt (H ++ [(s, t)]) j
    · rw [uB_neg S p F v ε j hj (KB.minusW ys a) _ fun hh' => hloc ⟨hh, hh'⟩, pj_zero_r (p v) j hj a ys _ hp, mul_zero]
    · rw [uB_neg S p F v ε j hj (KB.plusW ys a) _ hh, pj_zero_l (p v) j hj a ys _ hm, mul_zero]

end deg

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end

section
namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section blockL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

def uS (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (blk : ℕ × ℂ) (h : C.LPt) :
    Wd.Ix (Fin w.length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  uY S p F v ε j hj w (Y.image fun h => h ++ [blk]) (h ++ [blk])

theorem uS_mem (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (blk : ℕ × ℂ) (h : C.LPt) (hh : h ∈ Y) :
    uS S p F v ε j hj w Y blk h = uB S p F v ε j hj w (h ++ [blk]) :=
  uY_mem S p F v ε j hj w _ _ (Finset.mem_image_of_mem _ hh)

theorem glob_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g ∧ 0 < S.G.ka := by
  obtain ⟨hg1, hg2, -⟩ := hB
  refine ⟨by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2, ?_⟩
  unfold Sz.Glob.ka; rw [S.hv]; exact div_pos Real.pi_pos (by linarith [PBD.rd_pos' E])

theorem prod_ofFn_map' {K : ℕ} (g0 : Fin K → ℝ) (g : ℝ → ℝ) : ((List.ofFn g0).map g).prod = ∏ c, g (g0 c) := by
  rw [List.map_ofFn, List.prod_ofFn]; rfl

end blockL

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end

section
namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section consts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def lamLift (S : C.HidaSetting E Wp Wq) (b s : ℕ) (v : Fin S.f) : ℝ :=
  (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) * Real.exp 1 * (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) *
    J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)

theorem g_cast' (S : C.HidaSetting E Wp Wq) : ((S.g : ℕ) : ℝ) = S.G.g := by
  unfold C.HidaSetting.g Sz.Glob.g; push_cast; rfl

theorem len_eq' (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : S.cutHi v - S.cutLo v = S.G.lenI := by
  simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring

theorem norm_lamB' (S : C.HidaSetting E Wp Wq) (hg : 0 < S.G.g) (b s : ℕ) :
    ‖lamB S b s‖ = (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) := by
  have hg' : (0 : ℝ) < (S.g : ℝ) := by rw [g_cast']; exact hg
  rw [norm_lamB S hg' b s, g_cast', zpow_neg, ← inv_zpow, inv_div]

variable {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem lenI_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) : 0 < S.G.lenI := by
  have hGo := hB.2.2.2.2.2.2.2.2.2.2.1
  have h := (hGo v).1
  rw [len_eq'] at h
  have : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by have := PBD.ntop_ge S; positivity
  linarith

theorem lamLift_nonneg (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (v : Fin S.f) : 0 ≤ lamLift S b s v := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  have hN : (0 : ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hA := supA_nonneg S hg hk v false
  unfold lamLift
  have : 0 < 2 * Real.pi / S.G.g := by positivity
  positivity

theorem thr_lift (hCc : 28 * Real.exp 1 ≤ Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (hb : 1 ≤ b)
    (hs : 1 ≤ s) (hbs : b + s ≤ S.G.r + 1) (v : Fin S.f) :
    0 ≤ lamLift S b s v ∧ lamLift S b s v ≤ S.base.szL b s v := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  have hCA : Cc ≤ S.CA := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hN : (0:ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hcg : (0:ℝ) ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) := by positivity
  have h := (Formalism.FourierDecayAlt.P.frame_threshold_bound_holds (InfinitePlace E) S.G S.CA S.de S.de' S.T S.T' S.l (S.pl v) hg hl
    (hCc.trans hCA) (fun one => supA_nonneg S hg hk v one)).1 b s (Real.exp 1)
    ((28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s)) hb (Real.exp_pos 1).le le_rfl hcg le_rfl
  have hdec : decide (b = 1 ∧ s + 1 = 1) = false := decide_eq_false (by omega)
  rw [hdec] at h
  refine ⟨lamLift_nonneg hB b s v, ?_⟩
  show lamLift S b s v ≤ (if b + s ≤ S.G.r + 1 then _ else _)
  rw [if_pos hbs]
  unfold lamLift
  exact h

theorem lift_K (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (b s j K : ℕ) (hjb : b + s = j + 1)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ)
    (hl1 : ∀ c, ∑ i, |F7.lagCo (grid c) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * (j - s) + s)) :
    (∏ c, ∑ i, |F7.lagCo (grid c) i|) * ‖lamB S b s‖ ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)) ^ K ≤ (lamLift S b s v) ^ K := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  rw [norm_lamB' S hg b s]
  have hexp : 2 * (j - s) + s = 2 * (b - 1) + s := by omega
  have hl1' : ∀ c, ∑ i, |F7.lagCo (grid c) i| ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) := fun c =>
    (hl1 c).trans_eq (by rw [hexp, ntop_eq_N', len_eq'])
  unfold lamLift
  set cg := (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) with hcg
  set Tf := (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) with hTf
  set A := J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) with hA
  have hA0 : 0 ≤ A := supA_nonneg S hg hk v _
  have hgg : 0 < 2 * Real.pi / S.G.g := by positivity
  have hTf0 : 0 ≤ Tf := by positivity
  have hprod : (∏ c, ∑ i, |F7.lagCo (grid c) i|) ≤ cg ^ K := by
    calc (∏ c, ∑ i, |F7.lagCo (grid c) i|) ≤ ∏ _c : Fin K, cg :=
          Finset.prod_le_prod (fun c _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun c _ => hl1' c
      _ = cg ^ K := by simp
  have h1 : 0 ≤ Tf ^ K * (Real.exp 1 * A) ^ K := by positivity
  calc (∏ c, ∑ i, |F7.lagCo (grid c) i|) * Tf ^ K * (Real.exp 1 * A) ^ K
      = (∏ c, ∑ i, |F7.lagCo (grid c) i|) * (Tf ^ K * (Real.exp 1 * A) ^ K) := by ring
    _ ≤ cg ^ K * (Tf ^ K * (Real.exp 1 * A) ^ K) := mul_le_mul_of_nonneg_right hprod h1
    _ = (Tf * Real.exp 1 * cg * A) ^ K := by ring

theorem norm_u (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s K : ℕ) :
    ‖((((‖lamB S b s‖ : ℝ) : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ K)‖ = 1 := by
  rw [norm_pow, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), norm_pow,
    norm_neg, norm_one, one_pow, mul_one, mul_inv_cancel₀ (norm_ne_zero_iff.2 (lamB_ne S hg b s)), one_pow]

end consts

def LiftLocB : Prop :=
  P5.ThmPActual → KB.SizeStd → KB.DegLift → FormPos →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ Λ : ℕ → ℕ → Fin S.f → ℝ,
      (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ S.base.szL b s v) ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.LiftLoc (setC S p F) v fun b s => Λ b s v

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end
