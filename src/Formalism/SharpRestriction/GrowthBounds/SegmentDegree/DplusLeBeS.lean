import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeight
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeIffLtColH
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

section Kill

variable {R σ : Type} [CommRing R] (S : Set σ)

open Classical in

def kill : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun v => if v ∈ S then 0 else MvPolynomial.X v

open Classical in

def scaleS : MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  aeval fun v => if v ∈ S then Polynomial.X * Polynomial.C (MvPolynomial.X v) else Polynomial.C (MvPolynomial.X v)

open Classical in

def offDeg : (σ →₀ ℕ) →+ ℕ := Finsupp.liftAddHom fun v => if v ∈ S then AddMonoidHom.id ℕ else 0

theorem scaleS_monomial (m : σ →₀ ℕ) :
    scaleS (R := R) S (monomial m 1) = Polynomial.C (monomial m 1) * Polynomial.X ^ offDeg S m := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have : (monomial (f + g) (1 : R)) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul, hf, hg, map_add, pow_add, map_mul]
    ring
  | single v k =>
    rw [← MvPolynomial.X_pow_eq_monomial, map_pow]
    by_cases hv : v ∈ S
    · have h1 : scaleS (R := R) S (MvPolynomial.X v) = Polynomial.X * Polynomial.C (MvPolynomial.X v) := by
        simp [scaleS, hv]
      have h2 : offDeg S (Finsupp.single v k) = k := by simp [offDeg, hv]
      rw [h1, h2, mul_pow, Polynomial.C_pow, mul_comm]
    · have h1 : scaleS (R := R) S (MvPolynomial.X v) = Polynomial.C (MvPolynomial.X v) := by
        simp [scaleS, hv]
      have h2 : offDeg S (Finsupp.single v k) = 0 := by simp [offDeg, hv]
      rw [h1, h2, pow_zero, mul_one, Polynomial.C_pow]

theorem scaleS_coeff_zero (f : MvPolynomial σ R) : (scaleS S f).coeff 0 = kill S f := by
  classical
  have h : (Polynomial.constantCoeff.comp (scaleS (R := R) S : MvPolynomial σ R →+* Polynomial (MvPolynomial σ R))) =
      (kill (R := R) S : MvPolynomial σ R →+* MvPolynomial σ R) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [scaleS, kill, MvPolynomial.algebraMap_eq]
    · intro v
      by_cases hv : v ∈ S <;> simp [scaleS, kill, hv]
  have := congrArg (fun g => g f) h
  simpa [Polynomial.constantCoeff_apply] using this

theorem li_of_kill {ι : Type} (m : ι → σ →₀ ℕ) (w : ι → MvPolynomial σ R)
    (h : LinearIndependent R fun q => monomial (m q) (1 : R) * kill S (w q)) :
    LinearIndependent R fun q => monomial (m q) (1 : R) * w q := by
  classical
  rw [linearIndependent_iff'] at h ⊢
  intro s a hsum
  by_contra hne
  push Not at hne
  obtain ⟨q0, hq0s, hq0⟩ := hne
  let s' := s.filter fun q => a q ≠ 0
  have hs' : s'.Nonempty := ⟨q0, Finset.mem_filter.mpr ⟨hq0s, hq0⟩⟩
  obtain ⟨q1, hq1, hmin⟩ := Finset.exists_min_image s' (fun q => offDeg S (m q)) hs'
  set δ := offDeg S (m q1) with hδ
  have hsum' : ∑ q ∈ s', a q • (monomial (m q) (1 : R) * w q) = 0 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro q hq hq'
    have : a q = 0 := by
      by_contra hh
      exact hq' (Finset.mem_filter.mpr ⟨hq, hh⟩)
    rw [this, zero_smul]
  have hΘ := congrArg (fun P => (scaleS S P).coeff δ) hsum'
  simp only [map_sum, map_smul, map_mul, scaleS_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    map_zero, Polynomial.coeff_zero] at hΘ
  have hterm : ∀ q ∈ s', (Polynomial.C (monomial (m q) (1 : R)) * Polynomial.X ^ offDeg S (m q) *
      scaleS S (w q)).coeff δ = if offDeg S (m q) = δ then monomial (m q) (1 : R) * kill S (w q) else 0 := by
    intro q hq
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    have hle := hmin q hq
    split_ifs with h1 h2 h2
    · rw [h2, Nat.sub_self, scaleS_coeff_zero]
    · exact absurd (le_antisymm h1 hle) h2
    · exact absurd (le_of_eq h2) h1
    · rw [mul_zero]
  rw [Finset.sum_congr rfl fun q hq => by rw [hterm q hq]] at hΘ
  have hΘ' : ∑ q ∈ s'.filter (fun q => offDeg S (m q) = δ), a q • (monomial (m q) (1 : R) * kill S (w q)) = 0 := by
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) hΘ
    split_ifs <;> simp
  have := h _ a hΘ' q1 (Finset.mem_filter.mpr ⟨hq1, rfl⟩)
  exact (Finset.mem_filter.mp hq1).2 this

end Kill

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ)

omit [NeZero n'] in

def offSet (j : ℤ) : Set (ℤ × Fin (r + K)) :=
  {v | ∃ t c : Fin r, c ≠ Fin.rev t ∧ v = (X.F.fr j t.val, Fin.castAdd K c)}

omit [NeZero n'] in

def monTau (j : ℤ) (u : Fin r × Fin r → ℕ) : ℤ × Fin (r + K) →₀ ℕ :=
  ∑ v : Fin r × Fin r, Finsupp.single (X.F.fr j v.1.val, Fin.castAdd K v.2) (u v)

def wordEl (O : Type) [CommRing O] (j : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) : SegRing O r K :=
  segRen X.F j O (r + K) (PsiPl O (plPart q.1) (Ican (plPart q.1)) * PsiTan O (tanPart q.1) q.2.1)

end Dat

def RestKey (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b →
      LinearIndependent O fun q : X.Idx p K j (X.restr j b) =>
        monomial (X.monTau K j q.1.2.2) (1 : O) * kill (X.offSet K j) (X.wordEl K O j q.1)

theorem fr_injective {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) :
    Function.Injective fun a : Fin r => F.fr j a.val := by
  obtain ⟨-, -, h3, -⟩ := hV
  have key : ∀ d a : ℕ, a + d + 1 < r → F.fr j a < F.fr j (a + d + 1) := by
    intro d
    induction d with
    | zero => intro a h; exact h3 j a h
    | succ d ih => intro a h; exact lt_trans (ih a (by omega)) (h3 j (a + d + 1) (by omega))
  intro a b hab
  have hab' : F.fr j a.val = F.fr j b.val := hab
  by_contra hne
  have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
  have ha := a.isLt
  have hb := b.isLt
  rcases lt_or_gt_of_ne hne' with h | h
  · have := key (b.val - a.val - 1) a.val (by omega)
    rw [show a.val + (b.val - a.val - 1) + 1 = b.val by omega] at this
    exact absurd hab' (ne_of_lt this)
  · have := key (a.val - b.val - 1) b.val (by omega)
    rw [show b.val + (a.val - b.val - 1) + 1 = a.val by omega] at this
    exact absurd hab'.symm (ne_of_lt this)

theorem plEmb_injective (O : Type) [CommRing O] (r K : ℕ) : Function.Injective (plEmb O r K) := by
  apply rename_injective
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)

theorem restInd_of (C₀ : ℝ) (hK : RestKey C₀) : RestInd C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hB
  have h1 := li_of_kill (X.offSet K j) (fun q : X.Idx p K j (X.restr j b) => X.monTau K j q.1.2.2)
    (fun q => X.wordEl K O j q.1) (hK p n' r K X O S hX hLa hk j b hB)
  set c0 : MvPolynomial (ℤ × Fin r) O := X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) with hc0
  have hD : X.Dw O j ≠ 0 := Formalism.MainNotions.G.Joints.StandardMonomialSpace.detX_ne_zero _ (fr_injective X.F hX.valid (j - 1))
  have hc0ne : c0 ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ hD) (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_ne_zero _))
  have hc : plEmb O r K c0 ≠ 0 := (map_ne_zero_iff _ (plEmb_injective O r K)).mpr hc0ne
  have h2 := h1.map' (LinearMap.mulLeft O (plEmb O r K c0))
    (LinearMap.ker_eq_bot.mpr fun x y hxy => mul_left_cancel₀ hc hxy)
  have heq : (fun q : X.Idx p K j (X.restr j b) => X.famEl p K O j b q.1) =
      (⇑(LinearMap.mulLeft O ((plEmb O r K) c0)) ∘
        fun q : X.Idx p K j (X.restr j b) => (monomial (X.monTau K j q.1.2.2)) (1 : O) * X.wordEl K O j q.1) := by
    funext q
    simp only [Function.comp, LinearMap.mulLeft_apply]
    unfold Dat.famEl Dat.wordEl Dat.monTau
    rw [map_mul, ← hc0, mul_assoc]
    congr 2
    rw [MvPolynomial.monomial_sum_one, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_pow, ← MvPolynomial.X_pow_eq_monomial]
    simp [plEmb]
  rw [heq]
  exact h2

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs

variable {R : Type} [CommRing R] {N r : ℕ}

def stg (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) : Fin r → ℤ := if h : i < N + 1 then ν ⟨i, h⟩ else 0

theorem stg_eq (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) (h : i < N + 1) : ν ⟨i, h⟩ = stg ν i := by
  simp [stg, h]

theorem Kcol_succ (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (j : ℕ) (h : j < N) :
    Kcol R ν c (j + 1) =
      colStep c (colH (stg ν j) c) (colH (stg ν (j + 1)) c) (letVec R ⟨j, h⟩) (Kcol R ν c j) := by
  rw [Kcol, dif_pos h, stg_eq ν j (by omega), stg_eq ν (j + 1) (by omega)]

def offN (n0 : ℕ) : Set (Fin N × Fin r) := {v | n0 ≤ v.1.val ∧ v.2.val + (v.1.val - n0) + 1 ≠ r}

theorem kill_colStep (S : Set (Fin N × Fin r)) (c : ℤ) (hP hN : ℕ) (x : Fin r → MvPolynomial (Fin N × Fin r) R)
    (Kf : Finset (Fin r) → MvPolynomial (Fin N × Fin r) R) (J : Finset (Fin r)) :
    kill S (colStep c hP hN x Kf J) = colStep c hP hN (fun m => kill S (x m)) (fun J => kill S (Kf J)) J :=
  lift_colStep_map (kill (R := R) S : MvPolynomial (Fin N × Fin r) R →+* MvPolynomial (Fin N × Fin r) R) c hP hN x Kf J

theorem kill_X_not (S : Set (Fin N × Fin r)) (v : Fin N × Fin r) (hv : v ∉ S) :
    kill (R := R) S (MvPolynomial.X v) = MvPolynomial.X v := by
  simp [kill, hv]

theorem kill_X_mem (S : Set (Fin N × Fin r)) (v : Fin N × Fin r) (hv : v ∈ S) :
    kill (R := R) S (MvPolynomial.X v) = 0 := by
  simp [kill, hv]

theorem kill_Kcol_low (n0 : ℕ) (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ n0, ∀ J, kill (offN n0) (Kcol R ν c j J) = Kcol R ν c j J := by
  intro j
  induction j with
  | zero =>
    intro _ J
    exact lift_extOne_map (kill (R := R) (offN (N := N) (r := r) n0) :
      MvPolynomial (Fin N × Fin r) R →+* MvPolynomial (Fin N × Fin r) R) J
  | succ j ih =>
    intro hj J
    have hjN : j < N := by omega
    rw [Kcol_succ ν c j hjN, kill_colStep]
    have e1 : (fun m => kill (offN n0) (letVec R (N := N) (n := r) ⟨j, hjN⟩ m)) = letVec R ⟨j, hjN⟩ := by
      funext m
      apply kill_X_not
      intro hv
      have : n0 ≤ j := hv.1
      omega
    have e2 : (fun J => kill (offN n0) (Kcol R ν c j J)) = Kcol R ν c j := funext (ih (by omega))
    rw [e1, e2]

variable (n0 : ℕ) (hN : n0 + r = N)

def tauI (m : Fin r) : Fin N := ⟨n0 + (r - 1 - m.val), by have := m.isLt; omega⟩

def rises (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (i : ℕ) : Prop := colH (stg ν i) c < colH (stg ν (i + 1)) c

open Classical in

def riseA (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ) : Finset (Fin r) :=
  Finset.univ.filter fun m => r - 1 - m.val < t ∧ rises ν c (n0 + (r - 1 - m.val))

theorem kill_Kcol_tau (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (hc : 1 ≤ c)
    (hmono : ∀ t < r, colH (stg ν (n0 + t)) c ≤ colH (stg ν (n0 + t + 1)) c) :
    ∀ t ≤ r, ∀ J, riseA n0 ν c t ⊆ J → ∃ e : ℕ, kill (offN n0) (Kcol R ν c (n0 + t) J) =
      (-1) ^ e * (∏ m ∈ riseA n0 ν c t, MvPolynomial.X (tauI n0 hN m, m)) * Kcol R ν c n0 (J \ riseA n0 ν c t) := by
  classical
  intro t
  induction t with
  | zero =>
    intro _ J _
    refine ⟨0, ?_⟩
    have : riseA n0 ν c 0 = ∅ := by
      simp [riseA]
    rw [this]
    simp only [add_zero, pow_zero, Finset.prod_empty, mul_one, one_mul, Finset.sdiff_empty]
    exact kill_Kcol_low n0 (by omega) ν c n0 le_rfl J
  | succ t ih =>
    intro ht J hJ
    have htr : t < r := by omega
    have hjN : n0 + t < N := by omega
    let mt : Fin r := ⟨r - 1 - t, by omega⟩
    have hmt : r - 1 - mt.val = t := by simp only [mt]; omega
    have hval : ∀ m : Fin r, r - 1 - m.val = t → m = mt := by
      intro m hm
      apply Fin.ext
      have := m.isLt
      simp only [mt]; omega
    rw [show n0 + (t + 1) = n0 + t + 1 by ring, Kcol_succ ν c (n0 + t) hjN, kill_colStep]
    by_cases hr : rises ν c (n0 + t)
    · have hA : riseA n0 ν c (t + 1) = insert mt (riseA n0 ν c t) := by
        ext m
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases h3 : r - 1 - m.val = t
          · exact Or.inl (hval m h3)
          · exact Or.inr ⟨by omega, h2⟩
        · rintro (h | ⟨h1, h2⟩)
          · subst h
            rw [hmt]; exact ⟨by omega, hr⟩
          · exact ⟨by omega, h2⟩
      have hnot : mt ∉ riseA n0 ν c t := by
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h; rw [hmt] at h; omega
      have hmJ : mt ∈ J := hJ (by rw [hA]; exact Finset.mem_insert_self _ _)
      have hsub : riseA n0 ν c t ⊆ J.erase mt := by
        intro m hm
        refine Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hm), hJ (by rw [hA]; exact Finset.mem_insert_of_mem hm)⟩
      obtain ⟨e, he⟩ := ih (by omega) (J.erase mt) hsub
      have hstep : colStep c (colH (stg ν (n0 + t)) c) (colH (stg ν (n0 + t + 1)) c)
          (fun m => kill (offN n0) (letVec R (N := N) (n := r) ⟨n0 + t, hjN⟩ m))
          (fun J => kill (offN n0) (Kcol R ν c (n0 + t) J)) J =
          (-1) ^ (J.filter fun j => mt < j).card * MvPolynomial.X (tauI n0 hN mt, mt) *
            kill (offN n0) (Kcol R ν c (n0 + t) (J.erase mt)) := by
        have hr' : colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
        unfold colStep
        rw [if_pos hr', if_pos hc]
        unfold wedgeR
        rw [Finset.sum_eq_single mt]
        · congr 2
          have : (tauI n0 hN mt : Fin N) = ⟨n0 + t, hjN⟩ := by
            apply Fin.ext; simp only [tauI]; omega
          rw [this]
          apply kill_X_not
          intro hv
          apply hv.2
          simp only [mt]; omega
        · intro m _ hm
          have : kill (offN n0) (letVec R (N := N) (n := r) ⟨n0 + t, hjN⟩ m) = 0 := by
            apply kill_X_mem
            refine ⟨by simp, ?_⟩
            intro h
            apply hm
            apply hval
            simp only [add_tsub_cancel_left] at h
            omega
          beta_reduce
          rw [this]; ring
        · intro h; exact absurd hmJ h
      rw [hstep, he, hA, Finset.prod_insert hnot]
      refine ⟨(J.filter fun j => mt < j).card + e, ?_⟩
      have hset : J.erase mt \ riseA n0 ν c t = J \ insert mt (riseA n0 ν c t) := by
        ext m
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
        tauto
      rw [hset, pow_add]
      ring
    · have hA : riseA n0 ν c (t + 1) = riseA n0 ν c t := by
        ext m
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases h3 : r - 1 - m.val = t
          · rw [h3] at h2; exact absurd h2 hr
          · exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
      have heq : colH (stg ν (n0 + t)) c = colH (stg ν (n0 + t + 1)) c :=
        le_antisymm (hmono t htr) (not_lt.mp hr)
      rw [hA] at hJ ⊢
      obtain ⟨e, he⟩ := ih (by omega) J hJ
      refine ⟨e, ?_⟩
      unfold colStep
      rw [heq, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
      exact he

end Abs

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs2

variable {R : Type} [CommRing R] {N r : ℕ}

theorem colStep_same (c : ℤ) (h : ℕ) (x : Fin r → MvPolynomial (Fin N × Fin r) R)
    (Kf : Finset (Fin r) → MvPolynomial (Fin N × Fin r) R) : colStep c h h x Kf = Kf := by
  unfold colStep
  rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

theorem Kcol_const (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, (∀ i < j, colH (stg ν i) c = colH (stg ν (i + 1)) c) → Kcol R ν c j = extOne := by
  intro j
  induction j with
  | zero => intro _ _; rw [Kcol]
  | succ j ih =>
    intro hj h
    rw [Kcol_succ ν c j (by omega), h j (by omega), colStep_same]
    exact ih (by omega) fun i hi => h i (by omega)

def cutPath (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) : Fin (N + 1) → Fin r → ℤ := fun i => stg ν (min i.val n0)

theorem stg_cut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) (hi : i ≤ N) :
    stg (cutPath n0 ν) i = stg ν (min i n0) := by
  have : i < N + 1 := by omega
  simp [stg, cutPath, this]

theorem Kcol_cut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, Kcol R (cutPath n0 ν) c j = Kcol R ν c (min j n0) := by
  intro j
  induction j with
  | zero => intro _; rw [Nat.zero_min, Kcol, Kcol]
  | succ j ih =>
    intro hj
    rw [Kcol_succ _ c j (by omega), stg_cut n0 ν j (by omega), stg_cut n0 ν (j + 1) hj, ih (by omega)]
    by_cases h : j + 1 ≤ n0
    · rw [min_eq_left h, min_eq_left (by omega : j ≤ n0), Kcol_succ ν c j (by omega)]
    · rw [min_eq_right (by omega : n0 ≤ j + 1), min_eq_right (by omega : n0 ≤ j), colStep_same]

theorem colH_all {μ : Fin r → ℤ} {c : ℤ} (h : ∀ m, c ≤ μ m) : colH μ c = r := by
  unfold colH
  rw [Finset.filter_true_of_mem fun m _ => h m, Finset.card_univ, Fintype.card_fin]

theorem colH_none {μ : Fin r → ℤ} {c : ℤ} (h : ∀ m, μ m < c) : colH μ c = 0 := by
  unfold colH
  rw [Finset.filter_false_of_mem fun m _ => not_le.mpr (h m), Finset.card_empty]

theorem colH_anti (μ : Fin r → ℤ) {c c' : ℤ} (h : c ≤ c') : colH μ c' ≤ colH μ c := by
  unfold colH
  exact Finset.card_le_card fun m hm => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    omega

structure PlHyp (n0 : ℕ) (be : ℤ) (ν : Fin (N + 1) → Fin r → ℤ) : Prop where
  rng : ∀ i ≤ N, ∀ m, 0 ≤ stg ν i m ∧ stg ν i m ≤ be
  fin : ∀ m, stg ν N m = be
  up : ∀ t < r, ∀ c, colH (stg ν (n0 + t)) c ≤ colH (stg ν (n0 + t + 1)) c ∧
    colH (stg ν (n0 + t + 1)) c ≤ colH (stg ν (n0 + t)) c + 1

def mT (t : ℕ) (ht : t < r) : Fin r := ⟨r - 1 - t, by omega⟩

theorem riseA_succ_pos (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ) (ht : t < r)
    (hr : rises ν c (n0 + t)) :
    riseA n0 ν c (t + 1) = insert (mT t ht) (riseA n0 ν c t) ∧ mT t ht ∉ riseA n0 ν c t := by
  classical
  have hmt : r - 1 - (mT t ht).val = t := by simp only [mT]; omega
  constructor
  · ext m
    simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : r - 1 - m.val = t
      · left
        apply Fin.ext
        have := m.isLt
        simp only [mT]; omega
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · subst h
        rw [hmt]; exact ⟨by omega, hr⟩
      · exact ⟨by omega, h2⟩
  · simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h; rw [hmt] at h; omega

theorem riseA_succ_neg (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ)
    (hr : ¬ rises ν c (n0 + t)) : riseA n0 ν c (t + 1) = riseA n0 ν c t := by
  classical
  ext m
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h3 : r - 1 - m.val = t
    · rw [h3] at h2; exact absurd h2 hr
    · exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

theorem card_riseA {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    ∀ t ≤ r, colH (stg ν n0) c + (riseA n0 ν c t).card = colH (stg ν (n0 + t)) c := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    have : riseA n0 ν c 0 = ∅ := by simp [riseA]
    rw [this]; simp
  | succ t ih =>
    intro ht
    have htr : t < r := by omega
    have h := ih (by omega)
    obtain ⟨u1, u2⟩ := H.up t htr c
    by_cases hr : rises ν c (n0 + t)
    · obtain ⟨hA, hnot⟩ := riseA_succ_pos n0 ν c t htr hr
      rw [hA, Finset.card_insert_of_notMem hnot]
      have hr' : colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
      rw [show n0 + (t + 1) = n0 + t + 1 by ring]
      omega
    · rw [riseA_succ_neg n0 ν c t hr]
      have hr' : ¬ colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
      rw [show n0 + (t + 1) = n0 + t + 1 by ring]
      omega

theorem pEnd_eq (ν : Fin (N + 1) → Fin r → ℤ) : pEnd ν = stg ν N := by
  unfold pEnd
  rw [← stg_eq ν N (by omega)]
  rfl

theorem Ican_eq [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    Ican ν c = if 1 ≤ c ∧ c ≤ be then Finset.univ else ∅ := by
  classical
  have hbe : 0 ≤ be := by
    have := (H.rng N le_rfl 0).1
    rwa [H.fin] at this
  unfold Ican
  rw [pEnd_eq]
  by_cases h1 : 1 ≤ c
  · rw [if_pos h1]
    by_cases h2 : c ≤ be
    · rw [if_pos ⟨h1, h2⟩, colH_all fun m => by rw [H.fin]; exact h2]
      exact Finset.filter_true_of_mem fun m _ => m.isLt
    · rw [if_neg (fun h => h2 h.2), colH_none fun m => by rw [H.fin]; omega]
      exact Finset.filter_false_of_mem fun m _ => by omega
  · rw [if_neg h1, if_neg (fun h => h1 h.1), colH_all fun m => by rw [H.fin]; omega]
    exact Finset.filter_false_of_mem fun m _ => by have := m.isLt; omega

def Icut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) : ℤ → Finset (Fin r) := fun c => Ican ν c \ riseA n0 ν c r

theorem Kcol_inactive {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ)
    (hc : ¬ (1 ≤ c ∧ c ≤ be)) (j : ℕ) (hj : j ≤ N) : Kcol R ν c j = extOne := by
  apply Kcol_const ν c j hj
  intro i hi
  by_cases h1 : 1 ≤ c
  · have h2 : be < c := by
      by_contra h; exact hc ⟨h1, by omega⟩
    rw [colH_none fun m => lt_of_le_of_lt (H.rng i (by omega) m).2 h2,
      colH_none fun m => lt_of_le_of_lt (H.rng (i + 1) (by omega) m).2 h2]
  · rw [colH_all fun m => le_trans (by omega) (H.rng i (by omega) m).1,
      colH_all fun m => le_trans (by omega) (H.rng (i + 1) (by omega) m).1]

theorem extOne_empty {P : Type} [CommRing P] : (extOne (n := r) (P := P) ∅) = 1 := by
  simp [extOne]

theorem mem_colRange_of_le_entry (μ : Fin (N + 1) → Fin r → ℤ) (i : Fin (N + 1)) (m : Fin r) {c : ℤ} (h1 : 0 ≤ c)
    (h2 : c ≤ μ i m) : c ∈ colRange μ := by
  unfold colRange
  have hT : |μ i m| ≤ ∑ i, ∑ m, |μ i m| := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ m, |μ i m|)
      (fun i _ => Finset.sum_nonneg fun m _ => abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun m => |μ i m|) (fun m _ => abs_nonneg _) (Finset.mem_univ m)
  have := le_abs_self (μ i m)
  simp only [Finset.mem_Icc]
  constructor <;> omega

theorem Psi_full [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    Psi R ν (Ican ν) = ∏ c ∈ Finset.Icc 1 be, Kcol R ν c N Finset.univ := by
  classical
  unfold Psi
  symm
  have hsub : Finset.Icc 1 be ⊆ colRange ν := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    refine mem_colRange_of_le_entry ν (Fin.last N) 0 (by omega) ?_
    have := H.fin 0
    rw [← stg_eq ν N (by omega)] at this
    have h' : ν (Fin.last N) 0 = be := this
    rw [h']; exact hc.2
  rw [← Finset.prod_subset hsub]
  · refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_Icc] at hc
    rw [Ican_eq H, if_pos hc]
  · intro c _ hc
    rw [Finset.mem_Icc] at hc
    rw [Ican_eq H, if_neg hc, Kcol_inactive H c hc N le_rfl, extOne_empty]

theorem Psi_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    Psi R (cutPath n0 ν) (Icut n0 ν) = ∏ c ∈ Finset.Icc 1 be, Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) := by
  classical
  unfold Psi
  have hterm : ∀ c, Kcol R (cutPath n0 ν) c N (Icut n0 ν c) =
      if 1 ≤ c ∧ c ≤ be then Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) else 1 := by
    intro c
    rw [Kcol_cut n0 ν c N le_rfl, min_eq_right (by omega : n0 ≤ N)]
    unfold Icut
    rw [Ican_eq H]
    split_ifs with h
    · rfl
    · rw [Finset.empty_sdiff, Kcol_inactive H c h n0 (by omega), extOne_empty]
  rw [Finset.prod_congr rfl fun c _ => hterm c]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one]

  have hsub : (colRange (cutPath n0 ν)).filter (fun c => 1 ≤ c ∧ c ≤ be) ⊆ Finset.Icc 1 be := by
    intro c hc
    rw [Finset.mem_filter] at hc
    exact Finset.mem_Icc.mpr hc.2
  refine Finset.prod_subset hsub ?_
  intro c hc hnot
  rw [Finset.mem_Icc] at hc
  have hout : c ∉ colRange (cutPath n0 ν) := fun h => hnot (Finset.mem_filter.mpr ⟨h, hc⟩)
  have hlow : ∀ i ≤ n0, ∀ m, stg ν i m < c := by
    intro i hi m
    by_contra hge
    apply hout
    refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨i, by omega⟩ m (by omega) ?_
    have : cutPath n0 ν ⟨i, by omega⟩ m = stg ν i m := by
      simp [cutPath, min_eq_left hi]
    rw [this]; omega
  have h0 : colH (stg ν n0) c = 0 := colH_none (hlow n0 le_rfl)
  have hcard := card_riseA H c r le_rfl
  rw [h0, hN, colH_all fun m => by rw [H.fin]; exact hc.2, zero_add] at hcard
  have hall : riseA n0 ν c r = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard, Fintype.card_fin]
  rw [hall, Finset.sdiff_self, Kcol_const ν c n0 (by omega) fun i hi => by
    rw [colH_none (hlow i (by omega)), colH_none (hlow (i + 1) (by omega))], extOne_empty]

theorem kill_Psi [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    ∃ e : ℕ, kill (offN n0) (Psi R ν (Ican ν)) =
      (-1) ^ e * (∏ c ∈ Finset.Icc 1 be, ∏ m ∈ riseA n0 ν c r, MvPolynomial.X (tauI n0 hN m, m)) *
        Psi R (cutPath n0 ν) (Icut n0 ν) := by
  classical
  rw [Psi_full H, Psi_cut hN H, map_prod]
  have hcol : ∀ c ∈ Finset.Icc 1 be, ∃ e : ℕ, kill (offN n0) (Kcol R ν c N Finset.univ) =
      (-1) ^ e * (∏ m ∈ riseA n0 ν c r, MvPolynomial.X (tauI n0 hN m, m)) *
        Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    have := kill_Kcol_tau (R := R) n0 hN ν c hc.1 (fun t ht => (H.up t ht c).1) r le_rfl Finset.univ
      (Finset.subset_univ _)
    rwa [hN] at this
  choose! e he using hcol
  refine ⟨∑ c ∈ Finset.Icc 1 be, e c, ?_⟩
  rw [Finset.prod_congr rfl he, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

end Abs2

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs3

variable {N r : ℕ}

theorem Icut_eq [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    Icut n0 ν c = if 1 ≤ c ∧ c ≤ be then Finset.univ \ riseA n0 ν c r else ∅ := by
  classical
  unfold Icut
  rw [Ican_eq H]
  split_ifs
  · rfl
  · exact Finset.empty_sdiff _

theorem pEnd_cut {n0 : ℕ} (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) : pEnd (cutPath n0 ν) = stg ν n0 := by
  rw [pEnd_eq, stg_cut n0 ν N le_rfl, min_eq_right hn]

theorem riseA_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : Fin r) :
    (riseA n0 ν c r).filter (· ≤ t) = riseA n0 ν c r \ riseA n0 ν c (r - 1 - t.val) := by
  classical
  ext m
  have hm := m.isLt
  have ht := t.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, fun h4 => ?_⟩
    have : m.val ≤ t.val := h3
    omega
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    by_contra h4
    have h5 : t.val < m.val := not_le.mp h4
    exact h3 (by omega) h2

theorem riseA_mono (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {s t : ℕ} (h : s ≤ t) :
    riseA n0 ν c s ⊆ riseA n0 ν c t := by
  classical
  intro m
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨h1, h2⟩
  exact ⟨by omega, h2⟩

theorem card_Icut_filter [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (c : ℤ) (hc : 1 ≤ c ∧ c ≤ be) (t : Fin r) :
    ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + r =
      t.val + 1 + colH (stg ν (n0 + (r - 1 - t.val))) c := by
  classical
  have ht := t.isLt
  have h1 : ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + ((riseA n0 ν c r).filter (· ≤ t)).card =
      t.val + 1 := by
    rw [← Finset.card_union_of_disjoint]
    · have : (Finset.univ \ riseA n0 ν c r).filter (· ≤ t) ∪ (riseA n0 ν c r).filter (· ≤ t) = Finset.Iic t := by
        ext m
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_Iic]
        tauto
      rw [this, Fin.card_Iic]
    · rw [Finset.disjoint_left]
      intro m hm hm'
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm hm'
      exact hm.1 hm'.1
  have h2 : ((riseA n0 ν c r).filter (· ≤ t)).card + (riseA n0 ν c (r - 1 - t.val)).card = (riseA n0 ν c r).card := by
    rw [riseA_filter, Finset.card_sdiff_add_card_eq_card (riseA_mono n0 ν c (by omega))]
  have h3 := card_riseA H c r le_rfl
  have h4 := card_riseA H c (r - 1 - t.val) (by omega)
  have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact hc.2
  rw [hN, hNr] at h3
  omega

theorem isSt_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    IsSt (cutPath n0 ν) (Icut n0 ν) := by
  classical
  have hcard : ∀ c, (Icut n0 ν c).card =
      if 1 ≤ c then colH (pEnd (cutPath n0 ν)) c else r - colH (pEnd (cutPath n0 ν)) c := by
    intro c
    rw [pEnd_cut (by omega), Icut_eq H]
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1]
      by_cases h2 : c ≤ be
      · rw [if_pos ⟨h1, h2⟩, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        have h3 := card_riseA H c r le_rfl
        have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact h2
        rw [hN, hNr] at h3
        omega
      · rw [if_neg fun h => h2 h.2, Finset.card_empty,
          colH_none fun m => lt_of_le_of_lt (H.rng n0 (by omega) m).2 (by omega)]
    · rw [if_neg h1, if_neg fun h => h1 h.1, Finset.card_empty,
        colH_all fun m => le_trans (by omega) (H.rng n0 (by omega) m).1]
      omega
  refine ⟨?_, hcard, ?_⟩
  · intro c hc
    by_cases h : 1 ≤ c ∧ c ≤ be
    · rw [← Finset.card_eq_zero, hcard c, if_pos h.1, pEnd_cut (by omega)]
      apply colH_none
      intro m
      by_contra hge
      apply hc
      refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨n0, by omega⟩ m (by omega) ?_
      have : cutPath n0 ν ⟨n0, by omega⟩ m = stg ν n0 m := by simp [cutPath]
      rw [this]; omega
    · rw [Icut_eq H, if_neg h]
  · intro c t
    unfold tabCol
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1, if_pos (by omega : (1 : ℤ) ≤ c + 1), Icut_eq H, Icut_eq H]
      by_cases h2 : c + 1 ≤ be
      · rw [if_pos ⟨by omega, h2⟩, if_pos ⟨h1, by omega⟩]
        have e1 := card_Icut_filter hN H (c + 1) ⟨by omega, h2⟩ t
        have e2 := card_Icut_filter hN H c ⟨h1, by omega⟩ t
        have e3 := colH_anti (stg ν (n0 + (r - 1 - t.val))) (by omega : c ≤ c + 1)
        omega
      · rw [if_neg fun h => h2 h.2]
        simp
    · rw [if_neg h1]
      have hc0 : Icut n0 ν c = ∅ := by rw [Icut_eq H, if_neg fun h => h1 h.1]
      rw [hc0, Finset.sdiff_empty]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

theorem le_iff_lt_colH {μ : Fin r → ℤ} (hμ : Antitone μ) (c : ℤ) (m : Fin r) : c ≤ μ m ↔ m.val < colH μ c := by
  first | exact UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH .. | (apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ c m | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ c | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r

theorem eq_of_colH {μ μ' : Fin r → ℤ} (hμ : Antitone μ) (hμ' : Antitone μ') (h : ∀ c, colH μ c = colH μ' c) :
    μ = μ' := by
  funext m
  apply le_antisymm
  · rw [le_iff_lt_colH hμ', ← h, ← le_iff_lt_colH hμ]
  · rw [le_iff_lt_colH hμ, h, ← le_iff_lt_colH hμ']

theorem riseA_eq_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {t : ℕ} (ht : t ≤ r) :
    riseA n0 ν c t = (riseA n0 ν c r).filter fun m => r - 1 - m.val < t := by
  classical
  ext m
  have := m.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩
  · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩

theorem path_eq_of_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν ν' : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (H' : PlHyp n0 be ν') (hd : ∀ i, Antitone (ν i)) (hd' : ∀ i, Antitone (ν' i))
    (hcut : cutPath n0 ν = cutPath n0 ν') (hI : Icut n0 ν = Icut n0 ν') : ν = ν' := by
  classical
  have hlow : ∀ i ≤ n0, stg ν i = stg ν' i := by
    intro i hi
    have h1 := stg_cut n0 ν i (by omega)
    have h2 := stg_cut n0 ν' i (by omega)
    rw [min_eq_left hi] at h1 h2
    rw [← h1, ← h2, hcut]
  have hrise : ∀ c, 1 ≤ c ∧ c ≤ be → riseA n0 ν c r = riseA n0 ν' c r := by
    intro c hc
    have h1 := congrFun hI c
    rw [Icut_eq H, Icut_eq H', if_pos hc, if_pos hc] at h1
    have := congrArg (fun s => Finset.univ \ s) h1
    simpa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using this
  funext i
  rw [stg_eq ν i.val i.isLt, stg_eq ν' i.val i.isLt]
  by_cases hi : i.val ≤ n0
  · exact hlow i.val hi
  · obtain ⟨t, ht⟩ : ∃ t, i.val = n0 + t := ⟨i.val - n0, by omega⟩
    have hi' := i.isLt
    have htr : t ≤ r := by omega
    apply eq_of_colH
    · rw [← stg_eq ν i.val i.isLt]; exact hd i
    · rw [← stg_eq ν' i.val i.isLt]; exact hd' i
    intro c
    rw [ht]
    by_cases hc : 1 ≤ c ∧ c ≤ be
    · rw [← card_riseA H c t htr, ← card_riseA H' c t htr, hlow n0 le_rfl, riseA_eq_filter n0 ν c htr,
        riseA_eq_filter n0 ν' c htr, hrise c hc]
    · by_cases h1 : 1 ≤ c
      · have h2 : be < c := by
          by_contra h; exact hc ⟨h1, by omega⟩
        rw [colH_none fun m => lt_of_le_of_lt (H.rng _ (by omega) m).2 h2,
          colH_none fun m => lt_of_le_of_lt (H'.rng _ (by omega) m).2 h2]
      · rw [colH_all fun m => le_trans (by omega) (H.rng _ (by omega) m).1,
          colH_all fun m => le_trans (by omega) (H'.rng _ (by omega) m).1]

end Abs3

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem kill_rename {R σ τ : Type} [CommRing R] (f : σ → τ) (S : Set τ) (P : MvPolynomial σ R) :
    kill S (rename f P) = rename f (kill (f ⁻¹' S) P) := by
  have h : (kill S).comp (rename f) = (rename f).comp (kill (f ⁻¹' S) : MvPolynomial σ R →ₐ[R] _) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, rename_X, kill, aeval_X]
    by_cases h1 : f i ∈ S
    · have h2 : i ∈ f ⁻¹' S := h1
      rw [if_pos h1, if_pos h2, map_zero]
    · have h2 : i ∉ f ⁻¹' S := h1
      rw [if_neg h1, if_neg h2, rename_X]
  exact AlgHom.congr_fun h P

theorem kill_of_empty {R σ : Type} [CommRing R] (S : Set σ) (hS : S = ∅) (P : MvPolynomial σ R) : kill S P = P := by
  subst hS
  have h : (kill (∅ : Set σ) : MvPolynomial σ R →ₐ[R] _) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [kill]
  rw [h]
  rfl

theorem li_mono_words {R σ ι α : Type} [CommRing R] [IsDomain R] (Tset : Set σ) (w : α → MvPolynomial σ R)
    (hw : LinearIndependent R w) (M : ι → σ →₀ ℕ) (x : ι → α) (hM : ∀ q, ∀ v, M q v ≠ 0 → v ∈ Tset)
    (hsup : ∀ q, w (x q) ∈ supported R Tsetᶜ) (hinj : ∀ q q', M q = M q' → x q = x q' → q = q') :
    LinearIndependent R fun q => monomial (M q) (1 : R) * w (x q) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum q₀ hq₀
  obtain ⟨Φ, hΦmono⟩ : ∃ Φ : MvPolynomial σ R →ₗ[R] MvPolynomial σ R, ∀ (n : σ →₀ ℕ) (a : R),
      Φ (monomial n a) = if n.filter (· ∈ Tset) = M q₀ then monomial (n.filter (· ∉ Tset)) a else 0 := by
    refine ⟨(MvPolynomial.basisMonomials σ R).constr R (fun n : σ →₀ ℕ =>
      if n.filter (· ∈ Tset) = M q₀ then monomial (n.filter (· ∉ Tset)) (1 : R) else 0), fun n a => ?_⟩
    have e : monomial n a = a • (MvPolynomial.basisMonomials σ R) n := by
      simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, Module.Basis.constr_basis]
    split_ifs
    · rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    · rw [smul_zero]
  have hkey : ∀ q, Φ (monomial (M q) (1 : R) * w (x q)) = if M q = M q₀ then w (x q) else 0 := by
    intro q
    have hwsup := hsup q
    rw [mem_supported] at hwsup
    have hT : ∀ n ∈ (w (x q)).support, (M q + n).filter (· ∈ Tset) = M q ∧
        (M q + n).filter (· ∉ Tset) = n := by
      intro n hn
      have hnv : ∀ v, n v ≠ 0 → v ∉ Tset := fun v hv =>
        hwsup ((mem_vars v).2 ⟨n, hn, Finsupp.mem_support_iff.2 hv⟩)
      constructor
      · ext v
        rw [Finsupp.filter_apply, Finsupp.add_apply]
        by_cases hv : v ∈ Tset
        · rw [if_pos hv]
          have : n v = 0 := by
            by_contra h
            exact hnv v h hv
          rw [this, add_zero]
        · rw [if_neg hv]
          by_contra h
          exact hv (hM q v (Ne.symm h))
      · ext v
        rw [Finsupp.filter_apply, Finsupp.add_apply]
        by_cases hv : v ∈ Tset
        · rw [if_neg (not_not.2 hv)]
          by_contra h
          exact hnv v (Ne.symm h) hv
        · rw [if_pos hv]
          have : M q v = 0 := by
            by_contra h
            exact hv (hM q v h)
          rw [this, zero_add]
    conv_lhs => rw [(w (x q)).as_sum]
    rw [Finset.mul_sum, map_sum]
    simp only [monomial_mul, one_mul, hΦmono]
    split_ifs with hMq
    · conv_rhs => rw [(w (x q)).as_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [(hT n hn).1, (hT n hn).2, if_pos hMq]
    · refine Finset.sum_eq_zero fun n hn => ?_
      rw [(hT n hn).1, if_neg hMq]
  have hxinj : Function.Injective (fun q : {q // M q = M q₀} => x q.1) := by
    intro a b h
    exact Subtype.ext (hinj a.1 b.1 (a.2.trans b.2.symm) h)
  have hfib : LinearIndependent R (w ∘ fun q : {q // M q = M q₀} => x q.1) := hw.comp _ hxinj
  have h2 : ∑ q ∈ s, g q • (if M q = M q₀ then w (x q) else 0) = 0 := by
    have h := congrArg Φ hsum
    rw [map_sum, map_zero] at h
    calc ∑ q ∈ s, g q • (if M q = M q₀ then w (x q) else 0)
        = ∑ q ∈ s, Φ (g q • (monomial (M q) (1 : R) * w (x q))) :=
          Finset.sum_congr rfl fun q _ => by rw [map_smul, hkey]
      _ = 0 := h
  have h3 : ∑ q ∈ s.subtype (fun q => M q = M q₀), g q.1 • (w ∘ fun q : {q // M q = M q₀} => x q.1) q = 0 := by
    simp only [Function.comp_apply]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun q => g q • w (x q)), Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h2
    split_ifs <;> simp
  exact linearIndependent_iff'.1 hfib (s.subtype (fun q => M q = M q₀)) (fun q => g q.1) h3 ⟨q₀, rfl⟩
    (Finset.mem_subtype.2 hq₀)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Dict

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ}

theorem kfr_lt (hV : F.Valid L₁ N₁) (j : ℤ) {a b : ℕ} (hab : a < b) (hb : b < r) : F.fr j a < F.fr j b := by
  induction b with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
    · exact (ih h (by omega)).trans (hV.2.2.1 j k hb)
    · subst h
      exact hV.2.2.1 j a hb

theorem kfr_le (hV : F.Valid L₁ N₁) (j : ℤ) {a b : ℕ} (hab : a ≤ b) (hb : b < r) : F.fr j a ≤ F.fr j b := by
  rcases hab.lt_or_eq with h | h
  · exact (kfr_lt F hV j h hb).le
  · subst h
    exact le_rfl

theorem k_mem_letters (j x : ℤ) :
    x ∈ F.letters j ↔ (F.fr (j - 1) 0 ≤ x ∧ x ≤ F.fr j (r - 1)) ∧ posOf n' x ∈ F.TT := by
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]

theorem k_fr_mem_letters (hV : F.Valid L₁ N₁) (j : ℤ) {t : ℕ} (ht : t < r) : F.fr j t ∈ F.letters j := by
  rw [k_mem_letters]
  have h4 := hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h4
  have h5 := (hV.2.2.2.2.1 j t ht).1
  have a1 := kfr_le F hV (j - 1) (Nat.zero_le (r - 1)) (by omega)
  have a2 := kfr_le F hV j (Nat.zero_le t) ht
  have a3 := kfr_le F hV j (by omega : t ≤ r - 1) (by omega)
  exact ⟨⟨by omega, a3⟩, h5⟩

private theorem card_filter_lt_orderIsoOfFin_eq (s : Finset ℤ) {n : ℕ} (h : s.card = n) (i : Fin n) :
    (s.filter (fun y => y < ((s.orderIsoOfFin h i : s) : ℤ))).card = i.val := by
  set e := s.orderIsoOfFin h with he_def
  have hs : s.filter (fun y => y < ((e i : s) : ℤ)) =
      (Finset.Iio i).image (fun k => ((e k : s) : ℤ)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hy, hlt⟩
      obtain ⟨k, hk⟩ := e.surjective ⟨y, hy⟩
      refine ⟨k, ?_, by rw [hk]⟩
      have hkl : ((e k : s) : ℤ) < ((e i : s) : ℤ) := by
        rw [hk]
        exact hlt
      exact e.lt_iff_lt.mp (Subtype.coe_lt_coe.mp hkl)
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(e k).2, Subtype.coe_lt_coe.mpr (e.lt_iff_lt.mpr hk)⟩
  rw [hs, Finset.card_image_of_injective _ (fun a b hab => e.injective (Subtype.ext hab)), Fin.card_Iio]

private theorem filter_fr_le_letters_eq_image_Ico (hV : F.Valid L₁ N₁) (j : ℤ) {t : ℕ} (ht : t < r) :
    (F.letters j).filter (fun y => F.fr j t ≤ y) = (Finset.Ico t r).image (F.fr j) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨hx, htx⟩
    rw [k_mem_letters] at hx
    obtain ⟨⟨_, hxr⟩, hxT⟩ := hx
    have key : ∀ d u, r - 1 - u = d → u < r → F.fr j u ≤ x → ∃ a, (u ≤ a ∧ a < r) ∧ F.fr j a = x := by
      intro d
      induction d with
      | zero =>
        intro u hu hur hux
        have hu' : u = r - 1 := by omega
        subst hu'
        exact ⟨r - 1, ⟨le_rfl, hur⟩, le_antisymm hux hxr⟩
      | succ d ih =>
        intro u hu hur hux
        rcases hux.lt_or_eq with hlt | heq
        · have hu1 : u + 1 < r := by
            by_contra hc
            have hu2 : u = r - 1 := by omega
            subst hu2
            exact absurd hxr (not_le.mpr hlt)
          by_cases hnext : F.fr j (u + 1) ≤ x
          · obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := ih (u + 1) (by omega) hu1 hnext
            exact ⟨a, ⟨by omega, ha2⟩, ha3⟩
          · exact absurd hxT (hV.2.2.2.2.2.1 j u x hu1 hlt (not_le.mp hnext))
        · exact ⟨u, ⟨le_rfl, hur⟩, heq⟩
    exact key _ t rfl ht htx
  · rintro ⟨a, ⟨hta, har⟩, rfl⟩
    exact ⟨k_fr_mem_letters F hV j har, kfr_le F hV j hta har⟩

private theorem card_filter_lt_fr_add_sub_eq_segN (hV : F.Valid L₁ N₁) (j : ℤ) {t : ℕ} (ht : t < r) :
    ((F.letters j).filter (fun y => y < F.fr j t)).card + (r - t) = segN F j := by
  have h1 := Finset.card_filter_add_card_filter_not (s := F.letters j) (fun y => y < F.fr j t)
  have h2 : (F.letters j).filter (fun y => ¬ y < F.fr j t) =
      (F.letters j).filter (fun y => F.fr j t ≤ y) := by
    apply Finset.filter_congr
    intro y _
    exact not_lt
  rw [h2, filter_fr_le_letters_eq_image_Ico F hV j ht, Finset.card_image_of_injOn, Nat.card_Ico] at h1
  · exact h1
  · intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact (kfr_lt F hV j h hb.2).ne hab
    · exact (kfr_lt F hV j h ha.2).ne' hab

private theorem segE_eq_fr_iff' (hV : F.Valid L₁ N₁) (j : ℤ) (i : Fin (segN F j)) {t : ℕ} (ht : t < r) :
    segE F j i = F.fr j t ↔ i.val = segN F j - r + t := by
  have hcnt := card_filter_lt_fr_add_sub_eq_segN F hV j ht
  have h0 := card_filter_lt_fr_add_sub_eq_segN F hV j (t := 0) (by omega)
  have hA := card_filter_lt_orderIsoOfFin_eq (F.letters j) (rfl : (F.letters j).card = segN F j) i
  constructor
  · intro h
    have hE : segE F j i = (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) i :
        F.letters j) : ℤ) := rfl
    rw [← hE, h] at hA
    omega
  · intro h
    obtain ⟨k, hk⟩ := ((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j)).surjective
      ⟨F.fr j t, k_fr_mem_letters F hV j ht⟩
    have hB := card_filter_lt_orderIsoOfFin_eq (F.letters j) (rfl : (F.letters j).card = segN F j) k
    rw [hk] at hB
    dsimp only at hB
    have hki : k = i := Fin.ext (by omega)
    have hk2 : segE F j k = F.fr j t := by
      show (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) k : F.letters j) : ℤ) = _
      rw [hk]
    rw [← hki]
    exact hk2

theorem k_r_le_segN (hV : F.Valid L₁ N₁) (hr : 0 < r) (j : ℤ) : r ≤ segN F j := by
  have h0 := card_filter_lt_fr_add_sub_eq_segN F hV j (t := 0) hr
  omega

theorem segE_eq_fr_iff (hV : F.Valid L₁ N₁) (j : ℤ) (i : Fin (segN F j)) {t : ℕ} (ht : t < r) :
    segE F j i = F.fr j t ↔ i.val = segN F j - r + t := segE_eq_fr_iff' F hV j i ht

theorem segE_lt_fr_iff (hV : F.Valid L₁ N₁) (hr : 0 < r) (j : ℤ) (i : Fin (segN F j)) :
    segE F j i < F.fr j 0 ↔ i.val < segN F j - r := by
  obtain ⟨k, hk⟩ := ((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j)).surjective
    ⟨F.fr j 0, k_fr_mem_letters F hV j hr⟩
  have hseg : segE F j k = F.fr j 0 := by
    show (((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j) k : F.letters j) : ℤ) = _
    rw [hk]
  have hkv := (segE_eq_fr_iff' F hV j k hr).mp hseg
  rw [← hseg]
  refine (Subtype.coe_lt_coe.trans ((OrderIso.lt_iff_lt
    ((F.letters j).orderIsoOfFin (rfl : (F.letters j).card = segN F j))).trans
      Fin.lt_iff_val_lt_val)).trans ?_
  constructor <;> intro h <;> omega

end Dict

section Supp

variable {R : Type} [CommRing R] {N r : ℕ}

theorem Kcol_supported (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, ∀ J, Kcol R ν c j J ∈ supported R {v : Fin N × Fin r | v.1.val < j} := by
  intro j
  induction j with
  | zero =>
    intro _ J
    rw [Kcol.eq_1]
    unfold extOne
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ j ih =>
    intro hj J
    have hS : ∀ J', Kcol R ν c j J' ∈ supported R {v : Fin N × Fin r | v.1.val < j + 1} := by
      intro J'
      refine supported_mono (fun v hv => ?_) (ih (by omega) J')
      simp only [Set.mem_setOf_eq] at hv ⊢
      omega
    have hx : ∀ m, letVec R ⟨j, by omega⟩ m ∈ supported R {v : Fin N × Fin r | v.1.val < j + 1} := by
      intro m
      show X ((⟨j, by omega⟩ : Fin N), m) ∈ Algebra.adjoin R (X '' _)
      exact Algebra.subset_adjoin ⟨((⟨j, by omega⟩ : Fin N), m), by simp, rfl⟩
    rw [Kcol_succ ν c j (by omega)]
    unfold colStep wedgeR contrR
    split_ifs <;> first
      | exact hS J
      | exact sum_mem (fun m _ => mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) (hx m)) (hS _))

theorem Psi_cut_supported (n0 : ℕ) (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) (I : ℤ → Finset (Fin r)) :
    Psi R (cutPath n0 ν) I ∈ supported R {v : Fin N × Fin r | v.1.val < n0} := by
  unfold Psi
  refine prod_mem (fun c _ => ?_)
  rw [Kcol_cut n0 ν c N le_rfl, min_eq_right hn]
  exact Kcol_supported ν c n0 hn (I c)

end Supp

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Gen6

variable {N r : ℕ}

theorem stg_castSucc (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.castSucc = stg ν l.val := by
  unfold stg
  rw [dif_pos (by have := l.isLt; omega)]
  rfl

theorem stg_succ (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.succ = stg ν (l.val + 1) := by
  unfold stg
  rw [dif_pos (by have := l.isLt; omega)]
  rfl

theorem stg_plPart {K : ℕ} (μ : Fin (N + 1) → Fin (r + K) → ℤ) (i : ℕ) (m : Fin r) :
    stg (plPart μ) i m = stg μ i (Fin.castAdd K m) := by
  unfold stg
  split_ifs <;> rfl

theorem colH_step {ν ν' : Fin r → ℤ} (hν : Antitone ν) (hν' : Antitone ν') (ha : ∀ a, ν a ≤ ν' a)
    (hb : ∀ (a : Fin r) (h : a.val + 1 < r), ν' ⟨a.val + 1, h⟩ ≤ ν a) (c : ℤ) :
    colH ν c ≤ colH ν' c ∧ colH ν' c ≤ colH ν c + 1 := by
  constructor
  · unfold colH
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact le_trans hm (ha m)
  · unfold colH
    set S := Finset.univ.filter fun m => c ≤ ν m with hS
    set S' := Finset.univ.filter fun m => c ≤ ν' m with hS'
    have hsub : S'.image Fin.val ⊆ insert 0 (S.image fun a => a.val + 1) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S', S, Finset.mem_insert] at hx ⊢
      obtain ⟨m, hm, rfl⟩ := hx
      rcases Nat.eq_zero_or_pos m.val with h0 | hpos
      · left
        exact h0
      · right
        have hlt : m.val - 1 < r := by omega
        have h1 : (m.val - 1) + 1 < r := by omega
        have hm' : (⟨(m.val - 1) + 1, h1⟩ : Fin r) = m := Fin.ext (by simp; omega)
        refine ⟨⟨m.val - 1, hlt⟩, ?_, by simp; omega⟩
        have h2 := hb ⟨m.val - 1, hlt⟩ h1
        rw [hm'] at h2
        exact le_trans hm h2
    calc S'.card = (S'.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (insert 0 (S.image fun a => a.val + 1)).card := Finset.card_le_card hsub
      _ ≤ (S.image fun a => a.val + 1).card + 1 := Finset.card_insert_le _ _
      _ ≤ S.card + 1 := by
        have := Finset.card_image_le (s := S) (f := fun a : Fin r => a.val + 1)
        omega

theorem cut_ppath {LL : Letters (Fin N)} {b' : Fin N → ℕ} (P1 : PPath r N LL b') (n0 : ℕ) :
    ∃ bc, ∃ Pc : PPath r N LL bc, Pc.mu = cutPath n0 P1.mu := by
  classical
  have hdom : ∀ k, k < N + 1 → Antitone (stg P1.mu k) := by
    intro k hk
    rw [← stg_eq P1.mu k hk]; exact P1.dom _
  refine ⟨fun i => if i.val < n0 then b' i else 0, ⟨cutPath n0 P1.mu, ?_, ?_, ?_⟩, rfl⟩
  · show stg P1.mu (min (0 : Fin (N + 1)).val n0) = 0
    simp only [Fin.val_zero, Nat.zero_min]
    rw [← stg_eq P1.mu 0 (by omega)]
    exact P1.zero
  · intro i
    exact hdom _ (lt_of_le_of_lt (min_le_left _ _) i.isLt)
  · intro i
    have hi := i.isLt
    by_cases h : i.val < n0
    · have e1 : cutPath n0 P1.mu i.castSucc = P1.mu i.castSucc := by
        show stg P1.mu (min i.val n0) = _
        rw [min_eq_left (by omega), stg_castSucc P1.mu]
      have e2 : cutPath n0 P1.mu i.succ = P1.mu i.succ := by
        show stg P1.mu (min (i.val + 1) n0) = _
        rw [min_eq_left (by omega), stg_succ P1.mu]
      rw [e1, e2]
      simp only [h, if_true]
      exact P1.step i
    · have e1 : cutPath n0 P1.mu i.castSucc = stg P1.mu n0 := by
        show stg P1.mu (min i.val n0) = _
        rw [min_eq_right (by omega)]
      have e2 : cutPath n0 P1.mu i.succ = stg P1.mu n0 := by
        show stg P1.mu (min (i.val + 1) n0) = _
        rw [min_eq_right (by omega)]
      rw [e1, e2]
      simp only [h, if_false]
      have hs : HStrip (stg P1.mu n0) (stg P1.mu n0) 0 :=
        ⟨fun _ => le_rfl, fun a h' => hdom n0 (by omega) (by rw [Fin.le_def]; simp), by simp⟩
      split_ifs <;> exact hs

theorem joinPT_parts {K : ℕ} (μ : Fin (N + 1) → Fin (r + K) → ℤ) : joinPT (plPart μ) (tanPart μ) = μ := by
  funext i
  exact Fin.append_castAdd_natAdd

end Gen6

section Dat6

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

theorem dplus_le_beS (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) (hs : s ≤ segN X.F j - r) :
    T.dplus (segLL X.F j) dd s ≤ X.beS p K j b := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  unfold T.dplus Dat.beS
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
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

theorem plHyp_of (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) :
    PlHyp (segN X.F j - r) (X.beS p K j b : ℤ) (plPart μ) := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  obtain ⟨P, hPμ⟩ := hP.path
  have hrN : r ≤ segN X.F j := k_r_le_segN X.F hV hr j
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK

  have htau : ∀ t (ht : t < r), ∃ l : Fin (segN X.F j), l.val = segN X.F j - r + t ∧
      segE X.F j l = X.F.fr j t ∧ HStrip (stg μ (segN X.F j - r + t)) (stg μ (segN X.F j - r + t + 1)) (dd l) := by
    intro t ht
    let l : Fin (segN X.F j) := ⟨segN X.F j - r + t, by omega⟩
    have hl : segE X.F j l = X.F.fr j t := (segE_eq_fr_iff X.F hV j l ht).mpr rfl
    have hvec : (segLL X.F j).vec l = true := by
      rw [comb_vec, hl]; exact (hV.2.2.2.2.1 j t ht).2
    have hs := T.step_vec P l hvec
    rw [hPμ, stg_castSucc μ, stg_succ μ] at hs
    exact ⟨l, rfl, hl, hs⟩
  have hlow : ∀ i ≤ segN X.F j - r, ∀ m, stg μ i m ≤ (X.beS p K j b : ℤ) := by
    intro i hi m
    have h1 := T.mu_le_dplus P i (by omega) m
    rw [hPμ, stg_eq μ i (by omega)] at h1
    have h2 := dplus_le_beS X p K hX j b μ dd hP i hi
    exact le_trans h1 (by exact_mod_cast h2)
  have hup : ∀ t ≤ r, ∀ m, stg μ (segN X.F j - r + t) m ≤ (X.beS p K j b : ℤ) := by
    intro t
    induction t with
    | zero => intro _ m; exact hlow _ le_rfl m
    | succ t ih =>
      intro ht m
      obtain ⟨l, hlv, hl, hs⟩ := htau t (by omega)
      rw [show segN X.F j - r + (t + 1) = segN X.F j - r + t + 1 by ring]
      by_cases hm : m.val = 0
      · have := hP.head l ⟨t, by omega⟩ hl m (by omega)
        rw [stg_succ μ, hlv] at this
        rw [this]
      · have hm' := m.isLt
        have h2 := hs.2.1 ⟨m.val - 1, by omega⟩ (by simp only []; omega)
        have e : (⟨(⟨m.val - 1, by omega⟩ : Fin (r + K)).val + 1, by simp only []; omega⟩ : Fin (r + K)) = m :=
          Fin.ext (by simp only []; omega)
        rw [e] at h2
        exact le_trans h2 (ih (by omega) _)
  have hdom : ∀ k, k < segN X.F j + 1 → Antitone (stg (plPart μ) k) := by
    intro k hk a a' haa
    rw [stg_plPart, stg_plPart, ← stg_eq μ k hk, ← hPμ]
    exact P.dom _ (by rw [Fin.le_def]; simpa using haa)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi m
    rw [stg_plPart]
    constructor
    · have h1 := T.mu_nonneg P i (by omega) (Fin.castAdd K m) (by
        have := m.isLt
        simp only [Fin.val_castAdd]; omega)
      rwa [hPμ, stg_eq μ i (by omega)] at h1
    · by_cases h : i ≤ segN X.F j - r
      · exact hlow i h _
      · have := hup (i - (segN X.F j - r)) (by omega) (Fin.castAdd K m)
        rwa [show segN X.F j - r + (i - (segN X.F j - r)) = i by omega] at this
  · intro m
    rw [stg_plPart]
    obtain ⟨l, hlv, hl, -⟩ := htau (r - 1) (by omega)
    have := hP.head l ⟨r - 1, by omega⟩ hl (Fin.castAdd K m) (by
      have := m.isLt
      simp only [Fin.val_castAdd]; omega)
    rw [stg_succ μ, hlv, show segN X.F j - r + (r - 1) + 1 = segN X.F j by omega] at this
    exact this
  · intro t ht c
    obtain ⟨l, hlv, hl, hs⟩ := htau t ht
    refine colH_step (hdom _ (by omega)) (hdom _ (by omega)) ?_ ?_ c
    · intro a
      rw [stg_plPart, stg_plPart]
      exact hs.1 _
    · intro a h
      rw [stg_plPart, stg_plPart]
      have := hs.2.1 (Fin.castAdd K a) (by simp only [Fin.val_castAdd]; omega)
      exact this

end Dat6

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
