import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DplusLeBeS
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.OldestLetterInSegment
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.LDigits

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem rename_mem_supported {R σ τ : Type} [CommRing R] {f : σ → τ} {S : Set σ} {S' : Set τ}
    (h : ∀ v ∈ S, f v ∈ S') {P : MvPolynomial σ R} (hP : P ∈ supported R S) : rename f P ∈ supported R S' := by
  classical
  rw [mem_supported] at hP ⊢
  intro v hv
  have h1 := vars_rename f P (Finset.mem_coe.mp hv)
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h1
  exact h u (hP (Finset.mem_coe.mpr hu))

theorem sum_single_apply_zero {σ ι : Type} (s : Finset ι) (a : ι → σ) (k : ι → ℕ) (v : σ) (h : ∀ i ∈ s, a i ≠ v) :
    (∑ i ∈ s, Finsupp.single (a i) (k i)) v = 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finsupp.single_apply, if_neg (h i hi)]

section Fin7

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (K : ℕ)

def gp (j : ℤ) : Fin (segN X.F j) × Fin r → ℤ × Fin (r + K) := fun v => (segE X.F j v.1, Fin.castAdd K v.2)

def gt (j : ℤ) : Fin (segN X.F j) × Fin K → ℤ × Fin (r + K) := fun v => (segE X.F j v.1, Fin.natAdd r v.2)

theorem segRen_PsiPl (O : Type) [CommRing O] (j : ℤ) (ν : Fin (segN X.F j + 1) → Fin r → ℤ)
    (I : ℤ → Finset (Fin r)) :
    segRen X.F j O (r + K) (PsiPl O ν I) = rename (gp X K j) (Psi O ν I) := by
  unfold segRen PsiPl
  rw [rename_rename]
  rfl

theorem segRen_PsiTan (O : Type) [CommRing O] (j : ℤ) (κ : Fin (segN X.F j + 1) → Fin K → ℤ)
    (I : ℤ → Finset (Fin K)) :
    segRen X.F j O (r + K) (PsiTan O κ I) = rename (gt X K j) (Psi O κ I) := by
  unfold segRen PsiTan
  rw [rename_rename]
  rfl

def tauSet (j : ℤ) : Set (ℤ × Fin (r + K)) := {v | ∃ t c : Fin r, v = (X.F.fr j t.val, Fin.castAdd K c)}

theorem castAdd_ne_natAdd (a : Fin r) (c : Fin K) : Fin.castAdd K a ≠ Fin.natAdd r c := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  have := a.isLt
  omega

theorem gp_preimage {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ) :
    (gp X K j) ⁻¹' (X.offSet K j) = offN (segN X.F j - r) := by
  have hrN := k_r_le_segN X.F hV (NeZero.pos r) j
  ext v
  have hv1 := v.1.isLt
  constructor
  · rintro ⟨t, c, hc, hv⟩
    simp only [gp, Prod.mk.injEq] at hv
    have h1 := (segE_eq_fr_iff X.F hV j v.1 t.isLt).mp hv.1
    have h2 : v.2 = c := Fin.castAdd_injective _ _ hv.2
    refine ⟨by omega, fun h3 => hc ?_⟩
    apply Fin.ext
    rw [Fin.val_rev, ← h2]
    omega
  · rintro ⟨h1, h2⟩
    have ht : v.1.val - (segN X.F j - r) < r := by omega
    refine ⟨⟨v.1.val - (segN X.F j - r), ht⟩, v.2, ?_, ?_⟩
    · intro h3
      apply h2
      have := congrArg Fin.val h3
      rw [Fin.val_rev] at this
      simp only [] at this
      omega
    · simp only [gp, Prod.mk.injEq, and_true]
      exact (segE_eq_fr_iff X.F hV j v.1 ht).mpr (by omega)

theorem gt_preimage (j : ℤ) : (gt X K j) ⁻¹' (X.offSet K j) = ∅ := by
  ext v
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  rintro ⟨t, c, -, hv⟩
  simp only [gt, Prod.mk.injEq] at hv
  exact castAdd_ne_natAdd K c v.2 hv.2.symm

def dgT (j : ℤ) (n0 : ℕ) (hN : n0 + r = segN X.F j) (be : ℤ) (ν : Fin (segN X.F j + 1) → Fin r → ℤ) :
    ℤ × Fin (r + K) →₀ ℕ :=
  ∑ c ∈ Finset.Icc 1 be, ∑ m ∈ riseA n0 ν c r, Finsupp.single (gp X K j (tauI n0 hN m, m)) 1

theorem kill_wordEl (O : Type) [CommRing O] {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ)
    (hN : segN X.F j - r + r = segN X.F j) (be : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ))
    (H : PlHyp (segN X.F j - r) be (plPart q.1)) :
    ∃ e : ℕ, kill (X.offSet K j) (X.wordEl K O j q) =
      (-1) ^ e * monomial (dgT X K j (segN X.F j - r) hN be (plPart q.1)) (1 : O) *
        segRen X.F j O (r + K) (PsiPl O (cutPath (segN X.F j - r) (plPart q.1)) (Icut (segN X.F j - r) (plPart q.1)) *
          PsiTan O (tanPart q.1) q.2.1) := by
  classical
  obtain ⟨e, he⟩ := kill_Psi (R := O) hN H
  refine ⟨e, ?_⟩
  unfold Dat.wordEl
  rw [map_mul, map_mul, map_mul, segRen_PsiPl, segRen_PsiTan, segRen_PsiPl, kill_rename, kill_rename,
    gp_preimage X K hV j, kill_of_empty _ (gt_preimage X K j), he]
  simp only [map_mul, map_pow, map_neg, map_one, map_prod, rename_X]
  unfold dgT
  rw [MvPolynomial.monomial_sum_one]
  have : ∀ c ∈ Finset.Icc 1 be,
      monomial (∑ m ∈ riseA (segN X.F j - r) (plPart q.1) c r,
        Finsupp.single (gp X K j (tauI (segN X.F j - r) hN m, m)) 1) (1 : O) =
      ∏ m ∈ riseA (segN X.F j - r) (plPart q.1) c r, MvPolynomial.X (gp X K j (tauI (segN X.F j - r) hN m, m)) := by
    intro c _
    rw [MvPolynomial.monomial_sum_one]
    rfl
  rw [Finset.prod_congr rfl this]
  ring

theorem monTau_apply {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ) (u : Fin r × Fin r → ℕ) (t c : Fin r) :
    X.monTau K j u (X.F.fr j t.val, Fin.castAdd K c) = u (t, c) := by
  classical
  unfold Dat.monTau
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single (t, c)]
  · simp
  · intro v _ hv
    rw [Finsupp.single_apply, if_neg]
    intro h
    simp only [Prod.mk.injEq] at h
    exact hv (Prod.ext (fr_injective X.F hV j h.1) (Fin.castAdd_injective _ _ h.2))
  · intro h; exact absurd (Finset.mem_univ _) h

end Fin7

theorem restKey_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestKey C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hB
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have hN : segN X.F j - r + r = segN X.F j := Nat.sub_add_cancel hrN
  have h10 : BracketPolynomialSpan D := hAdm.2.2.2.2.2.2.2.2.2.1
  have h12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := (h12 p O S n' r K X.F X.L₁ X.N₁ j (fun _ => 0) (fun _ => 0) (fun _ => 0) hV hNK
    (fun _ => le_rfl)).2.1
  have hH : ∀ q : X.Idx p K j (X.restr j b),
      PlHyp (segN X.F j - r) (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) := by
    intro q
    obtain ⟨dd, hP, -⟩ := q.2
    exact plHyp_of X p K hX j _ _ dd hP
  have hpair : ∀ q : X.Idx p K j (X.restr j b), ∃ b' b'' : Fin (segN X.F j) → ℕ,
      (∃ P1 : PPath r (segN X.F j) (segLL X.F j) b', P1.mu = plPart q.1.1) ∧
      (∃ P2 : PPath K (segN X.F j) (segLL X.F j) b'', P2.mu = tanPart q.1.1) := by
    intro q
    obtain ⟨dd, hP, -⟩ := q.2
    obtain ⟨P, hPμ⟩ := hP.path
    obtain ⟨b', b'', -, h1, h2, -⟩ := (h10 (segN X.F j) r K (segLL X.F j) dd hNK (plPart q.1.1) (tanPart q.1.1)).mp
      ⟨P, by rw [hPμ, joinPT_parts]⟩
    exact ⟨b', b'', h1, h2⟩
  have hx : ∀ q : X.Idx p K j (X.restr j b),
      ((cutPath (segN X.F j - r) (plPart q.1.1), tanPart q.1.1) ∈ segPairsAll X.F j K) ∧
      IsSt (cutPath (segN X.F j - r) (plPart q.1.1)) (Icut (segN X.F j - r) (plPart q.1.1)) ∧
      IsSt (tanPart q.1.1) q.1.2.1 := by
    intro q
    obtain ⟨b', b'', ⟨P1, h1⟩, h2⟩ := hpair q
    obtain ⟨bc, Pc, hPc⟩ := cut_ppath P1 (segN X.F j - r)
    obtain ⟨dd, -, -, hSt, -⟩ := q.2
    exact ⟨⟨bc, b'', ⟨Pc, by rw [hPc, h1]⟩, h2⟩, isSt_cut hN (hH q), hSt⟩
  let x : X.Idx p K j (X.restr j b) →
      {x : ((Fin (segN X.F j + 1) → Fin r → ℤ) × (Fin (segN X.F j + 1) → Fin K → ℤ)) ×
        ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) //
        x.1 ∈ segPairsAll X.F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} := fun q =>
    ⟨((cutPath (segN X.F j - r) (plPart q.1.1), tanPart q.1.1),
      (Icut (segN X.F j - r) (plPart q.1.1), q.1.2.1)), hx q⟩
  let M : X.Idx p K j (X.restr j b) → (ℤ × Fin (r + K) →₀ ℕ) := fun q =>
    X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1)
  have htauI : ∀ m : Fin r, gp X K j (tauI (segN X.F j - r) hN m, m) ∈ tauSet X K j := by
    intro m
    have hm := m.isLt
    refine ⟨⟨r - 1 - m.val, by omega⟩, m, ?_⟩
    simp only [gp, Prod.mk.injEq, and_true]
    exact (segE_eq_fr_iff X.F hV j _ (by omega)).mpr rfl
  have hM : ∀ q, ∀ v, M q v ≠ 0 → v ∈ tauSet X K j := by
    intro q v hv
    by_contra hnot
    apply hv
    show (X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q.1.1)) v = 0
    rw [Finsupp.add_apply]
    have h1 : X.monTau K j q.1.2.2 v = 0 := by
      unfold Dat.monTau
      exact sum_single_apply_zero _ _ _ v fun i _ h => hnot ⟨i.1, i.2, h.symm⟩
    have h2 : dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) v = 0 := by
      unfold dgT
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      exact sum_single_apply_zero _ _ _ v fun m _ h => hnot (h ▸ htauI m)
    rw [h1, h2]
  have hsup : ∀ q, segRen X.F j O (r + K) (PsiPl O (x q).1.1.1 (x q).1.2.1 * PsiTan O (x q).1.1.2 (x q).1.2.2) ∈
      supported O (tauSet X K j)ᶜ := by
    intro q
    rw [map_mul, segRen_PsiPl, segRen_PsiTan]
    refine Subalgebra.mul_mem _ ?_ ?_
    · refine rename_mem_supported ?_ (Psi_cut_supported (segN X.F j - r) (by omega) (plPart q.1.1) _)
      rintro v hv ⟨t, c, h⟩
      simp only [gp, Prod.mk.injEq] at h
      have := (segE_eq_fr_iff X.F hV j v.1 t.isLt).mp h.1
      have hv' : v.1.val < segN X.F j - r := hv
      omega
    · refine rename_mem_supported (S := Set.univ) ?_ (by rw [supported_univ]; exact Algebra.mem_top)
      rintro v - ⟨t, c, h⟩
      simp only [gt, Prod.mk.injEq] at h
      exact castAdd_ne_natAdd K c v.2 h.2.symm
  have hinj : ∀ q q', M q = M q' → x q = x q' → q = q' := by
    intro q q' hMq hxq
    have hx' := congrArg Subtype.val hxq
    simp only [x, Prod.mk.injEq] at hx'
    obtain ⟨⟨hcut, hκ⟩, hI, hI''⟩ := hx'
    obtain ⟨b1, -, ⟨P1, h1⟩, -⟩ := hpair q
    obtain ⟨b2, -, ⟨P2, h2⟩, -⟩ := hpair q'
    have hν : plPart q.1.1 = plPart q'.1.1 :=
      path_eq_of_cut hN (hH q) (hH q') (fun i => by rw [← h1]; exact P1.dom i) (fun i => by rw [← h2]; exact P2.dom i)
        hcut hI
    have hμ : q.1.1 = q'.1.1 := by
      rw [← joinPT_parts q.1.1, ← joinPT_parts q'.1.1, hν, hκ]
    have hu0 : X.monTau K j q.1.2.2 = X.monTau K j q'.1.2.2 := by
      have h3 : X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q.1.1) =
          X.monTau K j q'.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q'.1.1) := hMq
      rw [hν] at h3
      exact add_right_cancel h3
    have hu : q.1.2.2 = q'.1.2.2 := by
      funext v
      rw [← monTau_apply X K hV j q.1.2.2 v.1 v.2, ← monTau_apply X K hV j q'.1.2.2 v.1 v.2, hu0]
    exact Subtype.ext (Prod.ext hμ (Prod.ext hI'' hu))
  have hli := li_mono_words (tauSet X K j) _ hw M x hM hsup hinj
  have hkill := fun q : X.Idx p K j (X.restr j b) =>
    kill_wordEl X K O hV j hN (X.beS p K j (X.restr j b) : ℤ) q.1 (hH q)
  choose e he using hkill
  have hli2 := hli.units_smul fun q => (-1 : Oˣ) ^ e q
  have heq : (fun q : X.Idx p K j (X.restr j b) =>
      monomial (X.monTau K j q.1.2.2) (1 : O) * kill (X.offSet K j) (X.wordEl K O j q.1)) =
      ((fun q => (-1 : Oˣ) ^ e q) • fun q => monomial (M q) (1 : O) *
        segRen X.F j O (r + K) (PsiPl O (x q).1.1.1 (x q).1.2.1 * PsiTan O (x q).1.1.2 (x q).1.2.2)) := by
    funext q
    rw [he q]
    simp only [Pi.smul_apply']
    rw [Units.smul_def, MvPolynomial.smul_eq_C_mul]
    have hmm : monomial (M q) (1 : O) = monomial (X.monTau K j q.1.2.2) (1 : O) *
        monomial (dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1)) (1 : O) := by
      rw [monomial_mul, one_mul]
    rw [hmm]
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, map_pow, map_neg, map_one]
    ring
  rw [heq]
  exact hli2

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def BetaRatioBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → 4 * X.Y * (X.beS p K j (X.restr j b) : ℝ) ≤ (X.Qc p K j : ℝ)

def TauDegreeOnPathBound : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K →
    ∀ (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) (dd : Fin (segN X.F j) → ℕ),
      X.IsPATH p K j b μ dd → ∀ i, X.F.fr j 0 ≤ segE X.F j i → dd i ≤ 2 * X.beS p K j b

def ResidueClassCount : Prop :=
  ∀ (r Q be c ρ : ℕ), 2 ≤ r → 2 * be < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 2 * r * be / Q) ≤
      (((Fintype.piFinset fun _ : Fin r => Finset.range (Q - 2 * be)).filter
        fun w => (c + ∑ i, w i) % Q = ρ % Q).card : ℝ)

section Congr

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ) [NeZero K]

theorem Bdeg_congr (j : ℤ) {b b' : ℤ → ℕ} (x : ℤ) (h : b x = b' x) : X.Bdeg p K j b x = X.Bdeg p K j b' x := by
  unfold Dat.Bdeg
  rw [h]

theorem beS_congr (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x) :
    X.beS p K j b = X.beS p K j b' := by
  unfold Dat.beS
  refine Finset.sum_congr rfl fun x hx => ?_
  exact Bdeg_congr X p K j x (h x (Finset.mem_filter.mp hx).2)

theorem IsPATH_congr (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x)
    {μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ} {dd : Fin (segN X.F j) → ℕ} (hP : X.IsPATH p K j b μ dd) :
    X.IsPATH p K j b' μ dd :=
  ⟨hP.path, fun i hi => by rw [hP.degs i hi]; exact Bdeg_congr X p K j _ (h _ hi),
    fun i i' hi m hm => by rw [hP.head i i' hi m hm, beS_congr X p K j h]⟩

theorem IsGood_congr (hX : X.Hyp p K) (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x)
    {μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ} (hG : X.IsGood p K j b μ) : X.IsGood p K j b' μ := by
  classical
  intro i hi
  have hlate : segE X.F j i ∈ X.toLate j := Finset.mem_filter.mpr ⟨segE_mem X.F j i, hi⟩
  have hold := (oldest_letter_in_segment p n' r K X hX j _ hlate).2
  have hth : X.thc p K j b' (segE X.F j i) = X.thc p K j b (segE X.F j i) := by
    unfold Dat.thc
    split_ifs with hW
    · rfl
    · have hLL := hold hW
      unfold Frames.LLset at hLL
      have hlt := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hLL).1).2
      rw [h _ hlt]
  rw [hth]
  exact hG i hi

theorem restr_setTau_low (j : ℤ) (b : ℤ → ℕ) (e : Fin r → ℕ) (x : ℤ) (hx : x < X.F.fr j 0) :
    X.restr j b x = X.restr j (X.setTau j b e) x := by
  unfold Dat.restr Dat.setTau
  have : ¬ (X.F.fr j 0 ≤ x ∧ x ≤ X.F.fr j (r - 1)) := fun h => by omega
  simp only [this, if_false]

theorem restr_setTau_tau (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (e : Fin r → ℕ) (i' : Fin r) :
    X.restr j (X.setTau j b e) (X.F.fr j i'.val) = e i' := by
  classical
  have hV := hX.valid
  have hmem := k_fr_mem_letters X.F hV j i'.isLt
  have h4 := hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h4
  have a2 := kfr_le X.F hV j (Nat.zero_le i'.val) i'.isLt
  have a3 := kfr_le X.F hV j (by have := i'.isLt; omega : i'.val ≤ r - 1) (by have := i'.isLt; omega)
  have hlate : X.F.fr j i'.val ∈ X.toLate j := by
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    unfold Frames.IsW
    omega
  unfold Dat.restr Dat.setTau
  rw [if_pos hlate, if_pos ⟨a2, a3⟩, Finset.sum_eq_single i']
  · simp
  · intro i _ hne
    rw [if_neg]
    intro h
    exact hne (fr_injective X.F hV j h).symm
  · intro h; exact absurd (Finset.mem_univ _) h

end Congr

theorem restMon_of (C₀ : ℝ) (h61 : BetaRatioBound C₀) (h21 : TauDegreeOnPathBound) (h63 : ResidueClassCount) : RestMon C₀ := by
  intro p n' r K _ _ _ X hX hLa hk j b hA hfin ρ
  classical
  have hV := hX.valid
  have hr : 0 < r := NeZero.pos r
  have hY : (1 : ℝ) ≤ X.Y := hX.Y1
  have hrhs : (0 : ℝ) ≤ ∑ e ∈ Fintype.piFinset fun i : Fin r =>
      (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j,
        (Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rcases le_or_gt (1 - (r : ℝ) / (2 * X.Y)) 0 with hneg | hpos
  · rw [max_eq_left hneg, mul_zero, zero_pow hr.ne', mul_zero]
    exact hrhs
  rw [max_eq_right hpos.le]
  set be := X.beS p K j (X.restr j b) with hbe
  set Q := X.Qc p K j with hQ
  have hQpos : 0 < Q := by
    rw [hQ]; unfold Dat.Qc
    exact pow_pos hX.prime.pos _
  have hbeQ : 4 * X.Y * (be : ℝ) ≤ (Q : ℝ) := h61 p n' r K X hX hLa hk j b hA
  have hbeQ' : 4 * be ≤ Q := by
    have : (4 : ℝ) * (be : ℝ) ≤ (Q : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) be]
    exact_mod_cast this
  obtain ⟨T, hT⟩ : ∃ T, Q = T + 2 * be := ⟨Q - 2 * be, by omega⟩
  have hTpos : 0 < T := by omega
  have hrN := k_r_le_segN X.F hV hr j
  let idxT : Fin r → Fin (segN X.F j) := fun i' => ⟨segN X.F j - r + i'.val, by have := i'.isLt; omega⟩
  have hidx : ∀ i', segE X.F j (idxT i') = X.F.fr j i'.val := fun i' =>
    (segE_eq_fr_iff X.F hV j _ i'.isLt).mpr rfl
  have := Fintype.ofFinite (X.Tset p K j (X.restr j b))
  let ddOf : X.Tset p K j (X.restr j b) → Fin (segN X.F j) → ℕ := fun τ => Classical.choose τ.2
  have hdd : ∀ τ : X.Tset p K j (X.restr j b), X.IsPATH p K j (X.restr j b) τ.1.1 (ddOf τ) ∧
      X.IsGood p K j (X.restr j b) τ.1.1 ∧ IsSt (tanPart τ.1.1) τ.1.2 := fun τ => Classical.choose_spec τ.2
  let dtau : X.Tset p K j (X.restr j b) → Fin r → ℕ := fun τ i' => ddOf τ (idxT i')
  have hdtau : ∀ τ i', dtau τ i' ≤ 2 * be := by
    intro τ i'
    refine h21 p n' r K X hX j _ _ _ (hdd τ).1 (idxT i') ?_
    rw [hidx]
    exact kfr_le X.F hV j (Nat.zero_le _) i'.isLt
  let Wfin : Finset (Fin r → ℕ) := Fintype.piFinset fun _ : Fin r => Finset.range T
  let Ufin : Finset (Fin r × Fin r → ℕ) := Fintype.piFinset fun _ : Fin r × Fin r => Finset.range T
  let φ : X.Tset p K j (X.restr j b) × (Fin r × Fin r → ℕ) → Fin r → ℕ := fun x i' =>
    dtau x.1 i' + ∑ c, x.2 (i', c)
  let A : Finset (X.Tset p K j (X.restr j b) × (Fin r × Fin r → ℕ)) :=
    ((Finset.univ : Finset (X.Tset p K j (X.restr j b))) ×ˢ Ufin).filter fun x => ∀ i', φ x i' % Q = ρ i' % Q
  set E := Fintype.piFinset fun i : Fin r => (Finset.range (r * Q)).filter fun e => e % Q = ρ i % Q with hE
  set cst : ℝ := (Q : ℝ) ^ (r - 1) * (1 - (r : ℝ) / (2 * X.Y)) with hcst
  have hcst0 : 0 ≤ cst := by positivity

  have hφE : ∀ x ∈ A, φ x ∈ E := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    have hu := (Finset.mem_product.mp hx1).2
    rw [Fintype.mem_piFinset] at hu
    rw [hE, Fintype.mem_piFinset]
    intro i'
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hx2 i'⟩
    have h1 : ∑ c, x.2 (i', c) ≤ r * (T - 1) := by
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin r)) (fun c => x.2 (i', c)) (T - 1) (by
        intro c _
        have := Finset.mem_range.mp (hu (i', c))
        omega)
      simpa using this
    have h2 := hdtau x.1 i'
    have h3 : r * (T - 1) + r = r * T := by
      obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    have h4 : 2 * be ≤ r * (2 * be) := Nat.le_mul_of_pos_left _ hr
    have h5 : r * Q = r * T + r * (2 * be) := by rw [hT]; ring
    show dtau x.1 i' + ∑ c, x.2 (i', c) < r * Q
    omega

  have hfib : ∀ e ∈ E, (A.filter fun x => φ x = e).card ≤ Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) := by
    intro e _
    have hlow := restr_setTau_low X j b e
    have hbe' : X.beS p K j (X.restr j (X.setTau j b e)) = be := (beS_congr X p K j hlow).symm
    have hfinI : Finite (X.Idx p K j (X.restr j (X.setTau j b e))) := by
      let g : X.Idx p K j (X.restr j (X.setTau j b e)) →
          X.Tset p K j (X.restr j b) × (Fin r × Fin r → Fin Q) := fun q =>
        (⟨(q.1.1, q.1.2.1), by
          obtain ⟨dd, h1, h2, h3, -⟩ := q.2
          exact ⟨dd, IsPATH_congr X p K j (fun x hx => (hlow x hx).symm) h1,
            IsGood_congr X p K hX j (fun x hx => (hlow x hx).symm) h2, h3⟩⟩,
          fun v => ⟨q.1.2.2 v, by
            obtain ⟨dd, -, -, -, h4, -⟩ := q.2
            have := h4 v
            omega⟩)
      refine Finite.of_injective g ?_
      intro q q' hqq
      have h1 : q.1.1 = q'.1.1 := congrArg (fun z => z.1.1.1) hqq
      have h2 : q.1.2.1 = q'.1.2.1 := congrArg (fun z => z.1.1.2) hqq
      refine Subtype.ext (Prod.ext h1 (Prod.ext h2 ?_))
      funext v
      exact congrArg (fun z => (z.2 v).val) hqq
    let g : {x // x ∈ A.filter fun x => φ x = e} → X.Idx p K j (X.restr j (X.setTau j b e)) := fun x =>
      ⟨(x.1.1.1.1, x.1.1.1.2, x.1.2), by
        obtain ⟨hxA, hxe⟩ := Finset.mem_filter.mp x.2
        obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hxA
        have hu := (Finset.mem_product.mp hx1).2
        rw [Fintype.mem_piFinset] at hu
        refine ⟨ddOf x.1.1, IsPATH_congr X p K j hlow (hdd x.1.1).1, IsGood_congr X p K hX j hlow (hdd x.1.1).2.1,
          (hdd x.1.1).2.2, ?_, ?_⟩
        · intro v
          rw [hbe']
          have := Finset.mem_range.mp (hu v)
          show x.1.2 v + 2 * be < Q
          omega
        · intro i i' hi
          have hii : i = idxT i' := (segE_strictMono X.F j).injective (hi.trans (hidx i').symm)
          rw [restr_setTau_tau X p K hX j b e i', hii]
          exact congrFun hxe i'⟩
    have hg : Function.Injective g := by
      intro x x' hxx
      have h1 : x.1.1.1.1 = x'.1.1.1.1 := congrArg (fun z => z.1.1) hxx
      have h2 : x.1.1.1.2 = x'.1.1.1.2 := congrArg (fun z => z.1.2.1) hxx
      have h3 : x.1.2 = x'.1.2 := congrArg (fun z => z.1.2.2) hxx
      exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h1 h2)) h3)
    have := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this

  have hcount : ∀ τ : X.Tset p K j (X.restr j b), cst ^ r ≤ ((A.filter fun x => x.1 = τ).card : ℝ) := by
    intro τ
    have h1 : ∀ i' : Fin r, cst ≤ ((Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card : ℝ) := by
      intro i'
      have h63' := h63 r Q be (dtau τ i') (ρ i') hX.r2 (by omega)
      rw [show Q - 2 * be = T by omega] at h63'
      refine le_trans ?_ h63'
      rw [hcst]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hQr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
      have hYp : (0 : ℝ) < X.Y := by linarith
      have : 2 * (r : ℝ) * (be : ℝ) / Q ≤ (r : ℝ) / (2 * X.Y) := by
        rw [div_le_div_iff₀ hQr (by positivity)]
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
        nlinarith
      linarith
    have h2 : (Fintype.piFinset fun i' : Fin r =>
        Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card ≤ (A.filter fun x => x.1 = τ).card := by
      refine Finset.card_le_card_of_injOn (fun w => (τ, fun v : Fin r × Fin r => w v.1 v.2)) ?_ ?_
      · intro w hw
        have hw' := Fintype.mem_piFinset.mp (Finset.mem_coe.mp hw)
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr fun v => ?_⟩, fun i' => ?_⟩, rfl⟩)
        · exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp (hw' v.1)).1 v.2
        · exact (Finset.mem_filter.mp (hw' i')).2
      · intro w _ w' _ hww
        simp only [Prod.mk.injEq, true_and] at hww
        funext a c
        exact congrFun hww (a, c)
    rw [Fintype.card_piFinset] at h2
    have h3 : cst ^ r ≤ ∏ i' : Fin r, ((Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card : ℝ) := by
      have : cst ^ r = ∏ _i' : Fin r, cst := by simp
      rw [this]
      exact Finset.prod_le_prod (fun _ _ => hcst0) fun i' _ => h1 i'
    refine le_trans h3 ?_
    exact_mod_cast h2
  have hA1 : A.card = ∑ τ : X.Tset p K j (X.restr j b), (A.filter fun x => x.1 = τ).card :=
    Finset.card_eq_sum_card_fiberwise fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  have hA2 : A.card = ∑ e ∈ E, (A.filter fun x => φ x = e).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx => Finset.mem_coe.mpr (hφE x (Finset.mem_coe.mp hx))
  have hstep1 : (Nat.card (X.Tset p K j (X.restr j b)) : ℝ) * cst ^ r ≤ (A.card : ℝ) := by
    rw [hA1, Nat.card_eq_fintype_card]
    push_cast
    have : (Fintype.card (X.Tset p K j (X.restr j b)) : ℝ) * cst ^ r =
        ∑ _τ : X.Tset p K j (X.restr j b), cst ^ r := by
      simp
    rw [this]
    exact Finset.sum_le_sum fun τ _ => hcount τ
  refine le_trans hstep1 ?_
  rw [hA2]
  push_cast
  exact Finset.sum_le_sum fun e he => by exact_mod_cast hfib e he

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem residue_class_count : ResidueClassCount := by
  classical
  intro r Q be c ρ hr hQ
  have hQ0 : 0 < Q := by omega
  have hcore := Formalism.InvariantFactorPaths.BranchingDimensions.residueClassLowerBound r Q be (ρ % Q + (Q - c % Q)) hr hQ
  refine le_trans hcore ?_
  have hle : ((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
      (fun u => (∑ l, (u l : ℕ)) % Q = (ρ % Q + (Q - c % Q)) % Q)).card ≤
      ((Fintype.piFinset fun _ : Fin r => Finset.range (Q - 2 * be)).filter
        fun w => (c + ∑ i, w i) % Q = ρ % Q).card := by
    refine Finset.card_le_card_of_injOn (fun u => fun l => (u l : ℕ)) ?_ ?_
    · intro u hu
      have hu' := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun l =>
        Finset.mem_range.mpr (u l).isLt, ?_⟩)
      have h1 : (∑ l, (u l : ℕ)) ≡ ρ % Q + (Q - c % Q) [MOD Q] := hu'
      have h2 : c + ∑ l, (u l : ℕ) ≡ c + (ρ % Q + (Q - c % Q)) [MOD Q] := Nat.ModEq.add_left c h1
      have h3 : c + (ρ % Q + (Q - c % Q)) ≡ ρ [MOD Q] := by
        have hc : c % Q < Q := Nat.mod_lt _ hQ0
        have e1 : c + (ρ % Q + (Q - c % Q)) = (c - c % Q + Q) + ρ % Q := by
          have := Nat.mod_le c Q
          omega
        rw [e1]
        have e2 : c - c % Q + Q ≡ 0 [MOD Q] := by
          have hd : Q ∣ c - c % Q := Nat.dvd_sub_mod c
          exact (Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.add hd (dvd_refl Q)))
        have e3 : ρ % Q ≡ ρ [MOD Q] := Nat.mod_modEq ρ Q
        simpa using e2.add e3
      exact h2.trans h3
    · intro u _ u' _ huu
      funext l
      exact Fin.ext (congrFun huu l)
  exact_mod_cast hle

theorem tele_le : ∀ (n : ℕ) (hn : 0 < n) (f g : Fin n → ℤ),
    (∀ (a : Fin n) (h : a.val + 1 < n), f ⟨a.val + 1, h⟩ ≤ g a) →
    ∑ a, (f a - g a) ≤ f ⟨0, hn⟩ - g ⟨n - 1, by omega⟩ := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  intro f g h
  rw [Finset.sum_sub_distrib, Fin.sum_univ_succ f, Fin.sum_univ_castSucc g]
  have h1 : ∑ i : Fin m, f i.succ ≤ ∑ i : Fin m, g i.castSucc :=
    Finset.sum_le_sum fun i _ => h i.castSucc (by simp)
  have e : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
  rw [e]
  have e0 : (⟨0, hn⟩ : Fin (m + 1)) = 0 := rfl
  rw [e0]
  linarith

section D21

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

theorem dminus_le_beS (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) :
    T.dminus (segLL X.F j) dd s ≤ X.beS p K j b := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  unfold T.dminus Dat.beS
  have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
      (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with h1 h2 h2
  · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
  · exfalso
    have hl := l.isLt
    have ht : l.val - (segN X.F j - r) < r := by omega
    have hseg : segE X.F j l = X.F.fr j (l.val - (segN X.F j - r)) :=
      (segE_eq_fr_iff X.F hV j l ht).mpr (by omega)
    have hvec : (segLL X.F j).vec l = true := by
      rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
    rw [hvec] at h1
    exact absurd h1.2 (by simp)
  · exact Nat.zero_le _
  · exact le_rfl

end D21

theorem tau_degree_on_path_bound : TauDegreeOnPathBound := by
  intro p n' r K _ _ _ X hX j b μ dd hP i hi
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  obtain ⟨P, hPμ⟩ := hP.path
  have hil := i.isLt
  have hnot : ¬ i.val < segN X.F j - r := fun h => by
    have := (segE_lt_fr_iff X.F hV hr j i).mpr h
    omega
  have ht : i.val - (segN X.F j - r) < r := by omega
  have hseg : segE X.F j i = X.F.fr j (i.val - (segN X.F j - r)) :=
    (segE_eq_fr_iff X.F hV j i ht).mpr (by omega)
  have hvec : (segLL X.F j).vec i = true := by
    rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
  have hs := T.step_vec P i hvec
  rw [hPμ] at hs
  have hn : 0 < r + K := by omega
  have h1 := tele_le (r + K) hn (μ i.succ) (μ i.castSucc) hs.2.1
  rw [hs.2.2] at h1
  have h2 : μ i.succ ⟨0, hn⟩ = (X.beS p K j b : ℤ) :=
    hP.head i ⟨i.val - (segN X.F j - r), ht⟩ hseg ⟨0, hn⟩ (Nat.zero_le _)
  have h3 := T.neg_dminus_le_mu P i.val (by omega) ⟨r + K - 1, by omega⟩
  rw [hPμ] at h3
  have h4 := dminus_le_beS X p K hX j b μ dd hP i.val
  have h5 : μ i.castSucc = μ ⟨i.val, by omega⟩ := rfl
  rw [h2, h5] at h1
  have h4' : (T.dminus (segLL X.F j) dd i.val : ℤ) ≤ (X.beS p K j b : ℤ) := by exact_mod_cast h4
  have : (dd i : ℤ) ≤ 2 * (X.beS p K j b : ℤ) := by linarith
  exact_mod_cast this

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
