import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeFamOf
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgePlane
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RankMulConductorDivLeOne
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.GoodRankOfPrim

section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem scale_zpow_mono (w : O) (hw : algebraMap O Kf w ≠ 0) {a b : ℤ} (hab : b ≤ a) (M : Submodule O X) :
    scale (algebraMap O Kf w ^ a) M ≤ scale (algebraMap O Kf w ^ b) M := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_scale.1 hx
  refine mem_scale.2 ⟨w ^ (a - b).toNat • y, M.smul_mem _ hy, ?_⟩
  rw [← algebraMap_smul Kf (w ^ (a - b).toNat) y, smul_smul, map_pow, ← zpow_natCast, ← zpow_add₀ hw]
  congr 2
  rw [Int.toNat_of_nonneg (by omega)]
  ring

theorem scale_mono (c : Kf) {M N : Submodule O X} (h : M ≤ N) : scale c M ≤ scale c N :=
  Submodule.map_mono h

end Scale

section Be

variable {Kf : Type} [Field Kf] {n' m : ℕ}

theorem be_add_left (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F F' : Vsp Kf lam0)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 (F + F') G = be p r lam0 F G + be p r lam0 F' G := by
  unfold be
  rw [smul_add, map_add]

theorem be_smulK_left (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (c : Kf) (F : Vsp Kf lam0)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 (c • F) G = c * be p r lam0 F G := by
  unfold be
  rw [smul_comm, map_smul, smul_eq_mul]

end Be

theorem edgeFamOf : EdgeFamOf := by
  intro D hM hBP hInc p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m r fl rest lam0 hnu h1 h2 e he nb n2 T oS tT D1
    cStar c' hc' hD Fvb Sy sh hF1 hF2 hF3 hSy hsh hT
  have hw := w_ne_zero hS
  have hdom : IsDominant lam0 := by
    rw [hnu]
    exact isDominant_add h1 h2
  let eqv : Fin nb × Fin n2 ≃ Fin (nb * n2) := finProdFinEquiv
  let Fs : Fin nb × Fin n2 → Vsp Kf lam0 := fun x => mulV hnu h1 h2 (Fvb x.1) (sh x.2)
  let Ss : Fin nb × Fin n2 → Vsp Kf lam0 := fun x => mulV hnu h1 h2 (Sy x.1) (sh x.2)
  have hdiff : ∀ x, Fs x - Ss x ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r lam0 e) := by
    intro x
    have hz : ((Fs x - Ss x : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ((Fvb x.1 - Sy x.1 : Vsp Kf fl) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
          ((sh x.2 : Vsp Kf rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      simp only [Fs, Ss, AddSubgroupClass.coe_sub, mulV_coe, sub_mul]
    have h0 : sh x.2 ∈ scale (algebraMap O Kf w ^ (0 : ℤ)) (Re p ι σ w r rest e) := by
      rw [zpow_zero]
      exact mem_scale.2 ⟨_, (hsh x.2).1, one_smul _ _⟩
    have h3 := Re_mul D hM p ι σ w hw r hnu h1 h2 e (c' : ℤ) 0 hz (hF2 x.1) h0
    rwa [add_zero] at h3
  have hSs : ∀ x, Ss x ∈ Re p ι σ w r lam0 e := fun x =>
    edge_lattice_mul_of_weight_sum D hM p ι σ w hw r hnu h1 h2 e (z := Ss x) rfl (hSy x.1) (hsh x.2).1
  refine ⟨fun i => Fs (eqv.symm i), ?_, ?_, ?_⟩
  · intro i
    constructor
    · have h3 := HL_mul (O := O) D hM ι σ hnu h1 h2 e.src (algebraMap O Kf w) hw (-(T : ℤ)) (-(oS : ℤ))
        (z := Fs (eqv.symm i)) rfl (hF1 _) (hsh _).2
      have e1 : (-(T : ℤ)) + (-(oS : ℤ)) = -((T + oS : ℕ) : ℤ) := by
        push_cast
        ring
      rwa [e1] at h3
    · have e2 : Fs (eqv.symm i) = Ss (eqv.symm i) + (Fs (eqv.symm i) - Ss (eqv.symm i)) := by abel
      show Fs (eqv.symm i) ∈ Re p ι σ w r lam0 e
      rw [e2]
      exact Submodule.add_mem _ (hSs _) (scale_pos_le w c' _ (hdiff _))
  · intro i e' he' hsrc hne
    have hI := (hInc p n' W Qq O Kf ι σ j w hS m r rest h2 e' he').1
    have hs : sh (eqv.symm i).2 ∈ scale (algebraMap O Kf w ^ (-(oS : ℤ))) (Re p ι σ w r rest e') := by
      apply scale_mono _ hI
      rw [hsrc]
      exact (hsh _).2
    have h3 := Re_mul D hM p ι σ w hw r hnu h1 h2 e' (c' : ℤ) (-(oS : ℤ)) (z := Fs (eqv.symm i)) rfl
      (hF3 _ e' he' hsrc hne) hs
    exact scale_zpow_mono w hw (by omega) _ h3
  · rintro c ⟨i0, hi0⟩
    obtain ⟨G, hG1, hG2, hG3, ⟨a, b, ha, hab⟩⟩ := hT (fun x => c (eqv x))
      ⟨eqv.symm i0, by simpa using hi0⟩
    refine ⟨G, hG1, hG2, hG3, ?_⟩
    have e1 : (∑ i, c i • Fs (eqv.symm i)) =
        (∑ x, c (eqv x) • Ss x) + ∑ x, c (eqv x) • (Fs x - Ss x) := by
      rw [← Finset.sum_add_distrib, ← Equiv.sum_comp eqv]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Equiv.symm_apply_apply, ← smul_add]
      congr 1
      abel
    have hE : (∑ x, c (eqv x) • (Fs x - Ss x)) ∈
        scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r lam0 e) :=
      Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hdiff x)
    obtain ⟨y, hy, hyE⟩ := mem_scale.1 hE
    obtain ⟨z, hz⟩ := ((hBP p n' W Qq O Kf ι σ j w hS m r lam0 hdom e he).1 G).1 hG2 y hy
    have hwc : w ^ c' = (p : O) ^ (D1 + 1) * w ^ (c' - 2 * (D1 + 1)) := by
      rw [← hS.w_sq, ← pow_mul, ← pow_add]
      congr 1
      omega
    obtain ⟨b', hb'⟩ := dvd_of_add (p : O) (p_nonunit hS) D1 a (w ^ (c' - 2 * (D1 + 1)) * z) ⟨b, hab.symm⟩
    refine ⟨a + (p : O) ^ (D1 + 1) * (w ^ (c' - 2 * (D1 + 1)) * z), b', ?_, hb'.symm⟩
    show be p r lam0 (∑ i, c i • Fs (eqv.symm i)) G = _
    rw [e1, be_add_left, ha, ← hyE, be_smulK_left, ← hz, zpow_natCast, ← map_pow, hwc]
    simp only [map_add, map_mul]
    ring

end Formalism.MainNotions.Pf14
end
end

section
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

theorem initial_level_nonneg {C Ct0 : ℝ} (hC : 0 ≤ C) (h0 : 0 ≤ Ct0) (p N N₁ L₁ G' k : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    0 ≤ t0 C Ct0 p N N₁ L₁ G' k a := by
  unfold t0 tableLineDegreeFive.La
  have hl : 0 ≤ Real.log a := Real.log_nonneg ha
  have ha0 : 0 ≤ a := by linarith
  positivity

theorem initial_level_mono_weights {C Ct0 Ct0' : ℝ} (hC : 0 ≤ C) (h : Ct0 ≤ Ct0') (p N N₁ L₁ G' k : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    t0 C Ct0 p N N₁ L₁ G' k a ≤ t0 C Ct0' p N N₁ L₁ G' k a := by
  unfold t0 tableLineDegreeFive.La
  have hl : 0 ≤ Real.log a := Real.log_nonneg ha
  have ha0 : 0 ≤ a := by linarith
  have hB : 0 ≤ C * (N₁ : ℝ) ^ 2 * Real.log a * a / (p * k) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + k * (p : ℝ) ^ G' := by
    positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hN) hB

theorem edgeStep_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg)
    (Ct0 CD1 C₂ C₃ : ℝ) (h0 : 0 < Ct0) (h1 : 0 < CD1)
    (hL3 : ∀ C : ℝ, C₂ ≤ C → SymbolRealisableBound C CLa) (hCl : ∀ C : ℝ, C₃ ≤ C → CloudStep C Ct0 CD1 CLa) :
    ∃ Ct0' CD1' Cr C₁ : ℝ, 0 < Ct0' ∧ 0 < CD1' ∧ 0 < Cr ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → EdgeStep C Ct0' CD1' Cr := by
  have hInc : DualHeightInclusion := hA.2.2.1
  have hBP : BePerfect := hA.2.2.2.1
  have h26 : Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hWI : WittIdent := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hM : tableLineDegreeFive.LevelPrimesProviso D := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨Cg, hCg1, hg2⟩ := symbol_space_at D CLa Ck Crk Cdeg h26
  refine ⟨max Ct0 |Cdeg|, CD1, max Crk 1, max Cg (max C₂ (max C₃ (max 2 (max |CLa| CD1)))),
    lt_of_lt_of_le h0 (le_max_left _ _), h1, lt_of_lt_of_le one_pos (le_max_right _ _),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro C hC
  have c1 : Cg ≤ C := le_trans (le_max_left _ _) hC
  have hC' := le_trans (le_max_right _ _) hC
  have c2 : C₂ ≤ C := le_trans (le_max_left _ _) hC'
  have hC'' := le_trans (le_max_right _ _) hC'
  have c3 : C₃ ≤ C := le_trans (le_max_left _ _) hC''
  have hC3 := le_trans (le_max_right _ _) hC''
  have c4 : 2 ≤ C := le_trans (le_max_left _ _) hC3
  have hC4 := le_trans (le_max_right _ _) hC3
  have c5 : |CLa| ≤ C := le_trans (le_max_left _ _) hC4
  have c6 : CD1 ≤ C := le_trans (le_max_right _ _) hC4
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H e he htgt
  have : Fact p.Prime := ⟨hSet.1.prime⟩
  have : NeZero n' := ⟨by have := hSet.1.two_le; omega⟩
  have hB := hyps_basic (C := C) (by linarith) H
  have hr2 : 2 ≤ r := H.2.1
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hcS : 8 * (Dp + 1) ≤ cStar := H.2.2.2.2.2.2.2.2.2.2.1
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  obtain ⟨K, hk⟩ : ∃ K, m + 1 = r + K := ⟨m + 1 - r, by omega⟩
  have : NeZero r := ⟨by omega⟩
  have : NeZero K := ⟨by omega⟩
  have hrk : r ≤ m + 1 := by omega
  have hw := w_ne_zero hSet.1
  have ha1 : (1 : ℝ) ≤ a := by linarith [hB.two_le_a]
  obtain ⟨φ, hφ⟩ := hWI p n' W Qq O Kf ι σ j w hSet.1
  obtain ⟨F, hF⟩ := frames_of TT r L₁ L₂ de h x hSet.1.even hr2 hB.one_le_depth_alt H.2.2.1
  have hTT := hF.1
  subst hTT
  let _ : Algebra (WF p n') O := algOfIdent j φ
  obtain ⟨E', hE', hL⟩ := hL3 C c2 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H
    φ hφ K hk hrk F hF
  have hG2 := hg2 C c1 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K hk F hF E'
    (fun t ht => (hE' t ht).1)
  obtain ⟨⟨Sg, hle, hcompl, ⟨ιb, b, hb⟩, hrank, _⟩, hdeg⟩ := hG2
  obtain ⟨B, hBgen, hBli, hBc⟩ := basis_fin Sg b hcompl
    (fun P => P ∈ Gen O p K F
      (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * F.TT.card))
        (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r F.TT.card c0 cpp cStar)) a Y)
      (G2d F (flatDeg lam0) E')) hb
  obtain ⟨hm, hhm, hsrc⟩ := he.1
  obtain ⟨hE1, _, _⟩ := edgePlane p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r hm hhm
  obtain ⟨g, hg, hbasis⟩ := hE1 e he hsrc
  set X : ℝ := Cdeg * (F.TT.card : ℝ) *
    (CLa * ((min (orbitWindowCount r de h x) (2 * F.TT.card) : ℕ) : ℝ) ^ 2 * Real.log a * a / ((p : ℝ) * ((r + K : ℕ) : ℝ)) +
      a * (p : ℝ) ^ (-(L₁ : ℤ)) + ((r + K : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x) with hX
  have hT : ∀ i, ∀ mm ∈ (B i).support, vsDeg mm ≤ ⌊X⌋₊ := fun i mm hmm =>
    Nat.le_floor (hdeg (B i) (Submodule.subset_span (hBgen i)) mm hmm)
  choose Fs hFs1 hFs2 using fun i => hL g hg (B i) (hBgen i) ⌊X⌋₊ (hT i)
  obtain ⟨Θ, hΘ, n2, oS, tT, D1, sh, hoS, htT, hD1, hsh, hcount, htests⟩ :=
    hCl C c3 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K hk hrk F hF E' hE'
      _ B hBgen hBli hBc e he htgt hm g hhm hg hbasis (fun i => ∑ o ∈ Finset.range (⌊X⌋₊ + 1), Fs i o)
      (by
        intro i
        rw [← hFs2 i, Submodule.coe_sum, map_sum])
  choose Fv hv1 hv2 hv3 using fun (i : Fin (Module.finrank O Sg)) (o : ℕ) =>
    flatSrc edgePlane p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r (dT F.TT lam0) hm hhm Θ hΘ g hg e hbasis
      (cPrime n' r F.TT.card c0 cpp cStar) o _ (Fs i o) (hFs1 i o).1 rfl (hFs1 i o).2.2
  obtain ⟨_, _, hn3, _⟩ := num C 1 CD1 1 one_pos h1 one_pos c4 (by linarith) c6 (by linarith) p n' m r F.TT L₁ L₂ de h x
    lam0 aT bT a Y cpp c0 Dp cStar H
  have hD1' : D1 ≤ Dp := by
    have : (D1 : ℝ) ≤ Dp := le_trans hD1 hn3
    exact_mod_cast this
  have hoS' : oS ≤ r * F.TT.card * c0 + 2 * r * n' * cpp := by
    have : (oS : ℝ) ≤ ((r * F.TT.card * c0 + 2 * r * n' * cpp : ℕ) : ℝ) := by
      refine le_trans hoS ?_
      unfold om
      push_cast
      exact le_refl _
    exact_mod_cast this
  have hfam := edgeFamOf D hM hBP hInc p n' W Qq O Kf ι σ j w hSet.1 m r (flW (dT F.TT lam0)) (restW F.TT lam0) lam0
    (lambda_zero_eq_product F.TT lam0) (flW_dom _) (restW_dom (by have := hB.m_ge; omega) F.TT lam0 hdom) e he
    (Module.finrank O Sg) n2 ⌊X⌋₊ oS tT D1 cStar (cPrime n' r F.TT.card c0 cpp cStar)
    (by unfold cPrime; omega) (by unfold cPrime; omega)
    (fun i => ∑ o ∈ Finset.range (⌊X⌋₊ + 1), Fv i o)
    (fun i => Θ (∑ o ∈ Finset.range (⌊X⌋₊ + 1), Fs i o)) sh
    (by
      intro i
      refine Submodule.sum_mem _ fun o ho => ?_
      rw [hsrc]
      exact scale_neg_mono w hw (Nat.lt_succ_iff.1 (Finset.mem_range.1 ho)) _ (hv1 i o))
    (by
      intro i
      rw [map_sum, ← Finset.sum_sub_distrib]
      exact Submodule.sum_mem _ fun o _ => hv2 i o)
    (by
      intro i e' he' hs' hne
      exact Submodule.sum_mem _ fun o _ => hv3 i o e' he' (hs'.trans hsrc) hne)
    (by
      intro i
      rw [map_sum]
      refine Submodule.sum_mem _ fun o _ => ?_
      exact scale_pos_le w 0 _ ((hΘ.2 g hg e hbasis (Fs i o) 0).1 (hFs1 i o).2.1))
    hsh
    (fun c hc => htests _ (fun _ _ => rfl) c hc)
  have hkR : ((r + K : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by rw [hk]
  have hXle : X ≤ t0 C (max Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    rw [hX, hkR]
    exact level_lower_bound_terms Cdeg CLa C (max Ct0 |Cdeg|) (le_max_right _ _) c5
      p F.TT.card (orbitWindowCount r de h x) (min (orbitWindowCount r de h x) (2 * F.TT.card)) L₁ (goodG' r de h x) (m + 1)
      (min_le_left _ _) (by have := H.1; omega) (by omega) a ha1
  have ht0 := initial_level_nonneg (C := C) (Ct0 := max Ct0 |Cdeg|) (by linarith) (le_trans h0.le (le_max_left _ _)) p F.TT.card
    (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) ha1
  have hTle : ((⌊X⌋₊ : ℕ) : ℝ) ≤ t0 C (max Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    rcases le_or_gt 0 X with hx0 | hx0
    · exact le_trans (Nat.floor_le hx0) hXle
    · rw [Nat.floor_of_nonpos hx0.le]
      simpa using ht0
  refine ⟨Module.finrank O Sg * n2, ⌊X⌋₊ + oS, tT, D1, ?_, ?_, hD1, ?_, hfam⟩
  · push_cast
    linarith
  · have := initial_level_mono_weights (C := C) (by linarith) (le_max_left Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x)
      (m + 1) ha1
    linarith
  · have hK : m + 1 - r = K := by omega
    have hp0 : (0 : ℝ) < p := by
      have : 0 < p := by have := H.1; omega
      exact_mod_cast this
    have hY : 0 < Y := by linarith [hB.two_le_Y]
    have hu : 0 ≤ (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ F.TT.card :=
      pow_nonneg (by linarith [rank_mul_conductor_div_le_one c4 H]) _
    have hPi : ∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (r + K) - 1) (r + K - 1) : ℕ) : ℝ) =
        ∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ) := by rw [hk]
    have hq : ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) = ((p : ℝ) ^ (n' * (r * (m + 1 - r))))⁻¹ := by
      rw [zpow_neg, zpow_natCast, ← pow_mul, hK]
    rw [hq, hPi, hkR] at hrank
    have := norm_index_count_bound Crk (max Crk 1) ((F.TT.card : ℝ) * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y)
      ((1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ F.TT.card) (dimV Kf lam0 : ℝ)
      (∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ))
      ((p : ℝ) ^ (n' * (r * (m + 1 - r)))) (Module.finrank O Sg) n2 (le_max_left _ _)
      (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) (Nat.cast_nonneg _)) hY.le) hu
      (Nat.cast_nonneg _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) (pow_pos hp0 _)
      (by
        refine le_trans (le_of_eq ?_) hrank
        ring)
      hcount
    refine le_trans (le_of_eq ?_) this
    ring

theorem restEdge_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hR3 : SourcesRealisable D CLa Ck Crk Cdeg CLa' CD Csz)
    (hRC : RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    RestEdge D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA h14a h14b
  obtain ⟨C₂, _, hL3⟩ := hR3 hA h14a
  obtain ⟨Ct0, CD1, C₃, h0, h1, _, hCl⟩ := hRC hA h14a h14b
  exact edgeStep_of D CLa Ck Crk Cdeg hA Ct0 CD1 C₂ C₃ h0 h1 hL3 hCl

end Formalism.MainNotions.Pf14
end
end
