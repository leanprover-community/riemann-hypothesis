import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev

section
open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl.Low

variable {R : Type*} [CommRing R]

def mnr (R : Type*) [CommRing R] {k n : ℕ} (h : n ≤ k) (ρ : Fin n → Fin k) :
    MvPolynomial (Fin k × Fin k) R :=
  (Matrix.of fun p q : Fin n => (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R)).det

lemma pMinor_eq {k : ℕ} (σ : Equiv.Perm (Fin k)) (n : ℕ) (h : n ≤ k) :
    pMinor R σ n h = mnr R h (σ ∘ Fin.castLE h) := rfl

lemma pMinor_congr {k : ℕ} (σ : Equiv.Perm (Fin k)) {n n' : ℕ} (e : n = n') (h : n ≤ k) (h' : n' ≤ k) :
    pMinor R σ n h = pMinor R σ n' h' := by
  subst e; rfl

lemma rowGen_X {k : ℕ} (a b : Fin k) (v : Fin k × Fin k) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  simp [rowGen]

lemma rowGen_mnr_mat {k n : ℕ} (h : n ≤ k) (a b : Fin k) (ρ : Fin n → Fin k) :
    rowGen R a b (mnr R h ρ) = (Matrix.of fun p q : Fin n =>
      Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R) +
      (if ρ p = b then Polynomial.X * Polynomial.C (X (a, Fin.castLE h q)) else 0)).det := by
  rw [mnr, AlgHom.map_det]
  congr 1
  ext p q
  simp [rowGen_X]

lemma C_mnr {k n : ℕ} (h : n ≤ k) (ρ : Fin n → Fin k) :
    (Polynomial.C (mnr R h ρ) : Polynomial (MvPolynomial (Fin k × Fin k) R)) =
      (Matrix.of fun p q : Fin n =>
        Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R)).det := by
  rw [mnr, RingHom.map_det]
  congr 1

lemma rowGen_mnr_of_not {k n : ℕ} (h : n ≤ k) (a b : Fin k) (ρ : Fin n → Fin k)
    (hb : ∀ p, ρ p ≠ b) : rowGen R a b (mnr R h ρ) = Polynomial.C (mnr R h ρ) := by
  rw [rowGen_mnr_mat, C_mnr]
  congr 1
  ext p q
  simp [hb p]

lemma rowGen_mnr_of_eq {k n : ℕ} (h : n ≤ k) (a b : Fin k) (ρ : Fin n → Fin k)
    (hρ : Function.Injective ρ) (p0 : Fin n) (hp0 : ρ p0 = b) :
    rowGen R a b (mnr R h ρ) = Polynomial.C (mnr R h ρ) +
      Polynomial.X * Polynomial.C (mnr R h (Function.update ρ p0 a)) := by
  classical
  set A : Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (Fin k × Fin k) R)) :=
    Matrix.of fun p q => Polynomial.C (X (ρ p, Fin.castLE h q)) with hA
  set v : Fin n → Polynomial (MvPolynomial (Fin k × Fin k) R) :=
    fun q => Polynomial.C (X (a, Fin.castLE h q)) with hv
  have h1 : (Matrix.of fun p q : Fin n =>
      Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R) +
      (if ρ p = b then Polynomial.X * Polynomial.C (X (a, Fin.castLE h q)) else 0)) =
      updateRow A p0 (A p0 + (Polynomial.X : Polynomial (MvPolynomial (Fin k × Fin k) R)) • v) := by
    ext p q
    by_cases hp : p = p0
    · subst hp; simp [hA, hv, hp0]
    · have : ρ p ≠ b := fun e => hp (hρ (e.trans hp0.symm))
      simp [hA, updateRow_ne hp, this]
  have h2 : updateRow A p0 v = Matrix.of fun p q : Fin n =>
      Polynomial.C (X (Function.update ρ p0 a p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R) := by
    ext p q
    by_cases hp : p = p0
    · subst hp; simp [hv]
    · simp [hA, updateRow_ne hp, Function.update_of_ne hp]
  rw [rowGen_mnr_mat, h1, det_updateRow_add, updateRow_eq_self, det_updateRow_smul, h2, C_mnr, C_mnr]

lemma mnr_update_eq_zero {k n : ℕ} (h : n ≤ k) (a : Fin k) (ρ : Fin n → Fin k) (p0 p1 : Fin n)
    (hne : p1 ≠ p0) (hp1 : ρ p1 = a) : mnr R h (Function.update ρ p0 a) = 0 := by
  classical
  rw [mnr]
  apply det_zero_of_row_eq (i := p0) (j := p1) hne.symm
  funext q
  simp [Function.update_of_ne hne, hp1]

lemma mnr_comp_swap {k n : ℕ} (h : n ≤ k) (ρ : Fin n → Fin k) (p q : Fin n) (hpq : p ≠ q) :
    mnr R h (ρ ∘ Equiv.swap p q) = - mnr R h ρ := by
  have e : (Matrix.of fun x y : Fin n =>
      (X ((ρ ∘ Equiv.swap p q) x, Fin.castLE h y) : MvPolynomial (Fin k × Fin k) R)) =
      (Matrix.of fun x y : Fin n =>
        (X (ρ x, Fin.castLE h y) : MvPolynomial (Fin k × Fin k) R)).submatrix (Equiv.swap p q) id := by
    ext x y; simp
  rw [mnr, e, det_permute, Equiv.Perm.sign_swap hpq]
  simp [mnr]

end PI.OddDualWeyl.Low

namespace PI.OddDualWeyl.Low

variable {R : Type*} [CommRing R]

lemma coeff_lin_pow {S : Type*} [CommRing S] (u v : S) (j : ℕ) :
    ((Polynomial.C u + Polynomial.X * Polynomial.C v) ^ j).coeff j = v ^ j := by
  have h : (Polynomial.C u + Polynomial.X * Polynomial.C v).natDegree ≤ 1 := by compute_degree
  have := Polynomial.coeff_pow_of_natDegree_le (m := j) h
  rw [mul_one] at this
  rw [this]
  congr 1
  rw [mul_comm]
  simp

lemma rowDiv_mem {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (j : ℕ)
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ weyl R r n hn ν) :
    rowDiv R a b j f ∈ weyl R r n hn ν := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨(a, b, j) :: w, rfl⟩
  | zero => simp [rowDiv]
  | add x y _ _ hx hy => simpa [rowDiv] using add_mem hx hy
  | smul c x _ hx => simpa [rowDiv] using Submodule.smul_mem _ c hx

lemma hw_mem {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : hw R hn ν ∈ weyl R r n hn ν :=
  Submodule.subset_span ⟨[], rfl⟩

lemma pw_one {k : ℕ} (ν : Fin k → ℕ) : pw R 1 ν = hw R le_rfl ν := rfl

section Step

variable {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)

lemma castLE_ne_of_lt {s : ℕ} (h : s ≤ n + 1) (p : Fin s) (j : Fin (n + 1)) (hj : p.val < j.val) :
    Fin.castLE h p ≠ j := by
  intro e; have := congrArg Fin.val e; simp at this; omega

lemma stepA (s : Fin (n + 1)) (hs : s.val < i.val) :
    rowGen R (σ i.succ) (σ i.castSucc) (pMinor R σ (s.val + 1) s.isLt) =
      Polynomial.C (pMinor R σ (s.val + 1) s.isLt) ∧
    pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt = pMinor R σ (s.val + 1) s.isLt := by
  constructor
  · rw [pMinor_eq]
    apply rowGen_mnr_of_not
    intro p hp
    exact castLE_ne_of_lt _ p _ (by simp; omega) (σ.injective hp)
  · rw [pMinor_eq, pMinor_eq]
    congr 1
    funext p
    simp only [Function.comp, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (castLE_ne_of_lt _ p _ (by simp; omega))
      (castLE_ne_of_lt _ p _ (by simp; omega))]

lemma stepB (s : Fin (n + 1)) (hs : s.val = i.val) :
    rowGen R (σ i.succ) (σ i.castSucc) (pMinor R σ (s.val + 1) s.isLt) =
      Polynomial.C (pMinor R σ (s.val + 1) s.isLt) +
      Polynomial.X * Polynomial.C (pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt) := by
  classical
  have hl : Fin.castLE s.isLt (Fin.last s.val) = i.castSucc := Fin.ext (by simp [hs])
  have key : (σ * Equiv.swap i.castSucc i.succ) ∘ Fin.castLE s.isLt =
      Function.update (σ ∘ Fin.castLE s.isLt) (Fin.last s.val) (σ i.succ) := by
    funext p
    by_cases hp : p = Fin.last s.val
    · subst hp
      simp only [Function.comp, Equiv.Perm.mul_apply, Function.update_self, hl, Equiv.swap_apply_left]
    · have hlt := Fin.val_lt_last hp
      rw [Function.update_of_ne hp]
      simp only [Function.comp, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (castLE_ne_of_lt _ p _ (by simp; omega))
        (castLE_ne_of_lt _ p _ (by simp; omega))]
  rw [pMinor_eq, pMinor_eq, key]
  exact rowGen_mnr_of_eq _ _ _ _ (σ.injective.comp (Fin.castLE_injective _)) _
    (by simp only [Function.comp, hl])

lemma stepC (s : Fin (n + 1)) (hs : i.val < s.val) :
    rowGen R (σ i.succ) (σ i.castSucc) (pMinor R σ (s.val + 1) s.isLt) =
      Polynomial.C (pMinor R σ (s.val + 1) s.isLt) ∧
    pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt = - pMinor R σ (s.val + 1) s.isLt := by
  classical
  set p0 : Fin (s.val + 1) := ⟨i.val, by omega⟩ with hp0
  set p1 : Fin (s.val + 1) := ⟨i.val + 1, by omega⟩ with hp1
  have h0 : Fin.castLE s.isLt p0 = i.castSucc := Fin.ext (by simp [hp0])
  have h1 : Fin.castLE s.isLt p1 = i.succ := Fin.ext (by simp [hp1])
  have hne : p1 ≠ p0 := by intro e; have := congrArg Fin.val e; simp [hp0, hp1] at this
  constructor
  · rw [pMinor_eq, rowGen_mnr_of_eq _ _ _ _ (σ.injective.comp (Fin.castLE_injective _)) p0
      (by simp only [Function.comp, h0]), mnr_update_eq_zero _ _ _ p0 p1 hne
      (by simp only [Function.comp, h1])]
    simp
  · have key : (σ * Equiv.swap i.castSucc i.succ) ∘ Fin.castLE s.isLt =
        (σ ∘ Fin.castLE s.isLt) ∘ Equiv.swap p0 p1 := by
      funext p
      simp only [Function.comp, Equiv.Perm.mul_apply]
      congr 1
      rw [← h0, ← h1, (Fin.castLE_injective s.isLt).swap_apply]
    rw [pMinor_eq, pMinor_eq, key, mnr_comp_swap _ _ _ _ hne.symm]

end Step

end PI.OddDualWeyl.Low

namespace PI.OddDualWeyl.Low

variable {R : Type*} [CommRing R]

theorem step {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) (ν : Fin (n + 1) → ℕ) :
    ∃ c : R, pw R (σ * Equiv.swap i.castSucc i.succ) ν =
      c • rowDiv R (σ i.succ) (σ i.castSucc) (ν i.castSucc - nuNext ν i.castSucc) (pw R σ ν) := by
  classical
  let m : Fin (n + 1) → MvPolynomial (Fin (n + 1) × Fin (n + 1)) R :=
    fun s => pMinor R σ (s.val + 1) s.isLt
  let m' : Fin (n + 1) → MvPolynomial (Fin (n + 1) × Fin (n + 1)) R :=
    fun s => pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt
  let c : Fin (n + 1) → ℕ := fun s => ν s - nuNext ν s
  let ε : Fin (n + 1) → R := fun s => if i.val < s.val then -1 else 1
  have hne : ∀ s, s ≠ i.castSucc → rowGen R (σ i.succ) (σ i.castSucc) (m s) = Polynomial.C (m s) ∧
      m' s = MvPolynomial.C (ε s) * m s := by
    intro s hs
    have : s.val ≠ i.val := fun e => hs (Fin.ext (by simp [e]))
    rcases Nat.lt_or_gt_of_ne this with h | h
    · obtain ⟨h1, h2⟩ := stepA (R := R) σ i s h
      refine ⟨h1, ?_⟩
      simp only [m', m, ε, h2, if_neg (by omega : ¬ i.val < s.val), map_one, one_mul]
    · obtain ⟨h1, h2⟩ := stepC (R := R) σ i s h
      refine ⟨h1, ?_⟩
      simp only [m', m, ε, h2, if_pos h, map_neg, map_one, neg_one_mul]
  have hI : rowGen R (σ i.succ) (σ i.castSucc) (m i.castSucc) =
      Polynomial.C (m i.castSucc) + Polynomial.X * Polynomial.C (m' i.castSucc) :=
    stepB (R := R) σ i i.castSucc (by simp)
  have hrd : rowDiv R (σ i.succ) (σ i.castSucc) (c i.castSucc) (pw R σ ν) =
      m' i.castSucc ^ c i.castSucc * ∏ s ∈ Finset.univ.erase i.castSucc, m s ^ c s := by
    show (rowGen R (σ i.succ) (σ i.castSucc) (∏ s, m s ^ c s)).coeff (c i.castSucc) = _
    rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i.castSucc)]
    rw [Finset.prod_congr rfl (fun s hs => by
      rw [map_pow, (hne s (Finset.ne_of_mem_erase hs)).1])]
    rw [map_pow, hI, show ∏ s ∈ Finset.univ.erase i.castSucc, (Polynomial.C (m s)) ^ c s =
      Polynomial.C (∏ s ∈ Finset.univ.erase i.castSucc, m s ^ c s) by simp [map_prod, map_pow],
      Polynomial.coeff_mul_C, coeff_lin_pow]
  refine ⟨∏ s ∈ Finset.univ.erase i.castSucc, ε s ^ c s, ?_⟩
  rw [show ν i.castSucc - nuNext ν i.castSucc = c i.castSucc from rfl, hrd, ← MvPolynomial.C_mul']
  show ∏ s, m' s ^ c s = _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i.castSucc)]
  rw [Finset.prod_congr rfl (fun s hs => by rw [(hne s (Finset.ne_of_mem_erase hs)).2])]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  ring

theorem pw_mem {n : ℕ} (ν : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    pw R σ ν ∈ weyl R (n + 1) (n + 1) le_rfl ν := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  refine Submonoid.closure_induction_right
    (motive := fun x _ => pw R x ν ∈ weyl R (n + 1) (n + 1) le_rfl ν) ?_ ?_ hσ
  · rw [pw_one]; exact hw_mem _ _
  · intro x _ y hy ih
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨c, hc⟩ := step (R := R) x i ν
    rw [hc]
    exact Submodule.smul_mem _ c (rowDiv_mem _ _ _ _ _ ih)

end PI.OddDualWeyl.Low

namespace PI.OddDualWeyl

theorem lowestWeightMem : LowMem := by
  intro R _ k ν
  cases k with
  | zero =>
    have : low R ν = hw R (le_refl 0) ν := by simp [low, pw, hw]
    rw [this]; exact Low.hw_mem _ _
  | succ n => exact Low.pw_mem ν _

end PI.OddDualWeyl
end
end

section
open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl.LowA

variable {R : Type*} [CommRing R]

lemma nuNext_castSucc {m : ℕ} (ν : Fin (m + 1) → ℕ) (t : Fin m) : nuNext ν t.castSucc = ν t.succ := by
  have ht := t.isLt
  have h : (t.castSucc : Fin (m + 1)).val + 1 < m + 1 := by rw [Fin.val_castSucc]; omega
  unfold PI.OddDualWeyl.nuNext
  rw [dif_pos h]
  congr 1

lemma nuNext_last {m : ℕ} (ν : Fin (m + 1) → ℕ) : nuNext ν (Fin.last m) = 0 := by
  unfold PI.OddDualWeyl.nuNext
  rw [dif_neg (by simp)]

lemma nuStar_apply {m : ℕ} (lam : Fin (m + 1) → ℤ) (t : Fin (m + 1)) :
    nuOf (lamStar lam) t = (lam 0 - lam t.rev).toNat := by
  simp only [PI.OddDualWeyl.nuOf, PI.OddDualWeyl.lamStar, Fin.rev_last]
  congr 1
  ring

lemma nu_anti {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (t : Fin m) :
    nuOf lam t.succ ≤ nuOf lam t.castSucc := by
  have h := hlam (show t.castSucc ≤ t.succ from Fin.castSucc_lt_succ.le)
  exact Int.toNat_le_toNat (by omega)

lemma expo_castSucc {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (s : Fin m) :
    nuOf (lamStar lam) s.castSucc - nuNext (nuOf (lamStar lam)) s.castSucc =
      nuOf lam s.rev.castSucc - nuNext (nuOf lam) s.rev.castSucc := by
  rw [nuNext_castSucc, nuNext_castSucc]
  simp only [nuStar_apply, Fin.rev_castSucc, Fin.rev_succ]
  simp only [PI.OddDualWeyl.nuOf]
  have h1 := hlam (Fin.zero_le s.rev.castSucc)
  have h2 := hlam (show s.rev.castSucc ≤ s.rev.succ from Fin.castSucc_lt_succ.le)
  have h3 := hlam (Fin.le_last s.rev.succ)
  omega

lemma expo_star_last {m : ℕ} (lam : Fin (m + 1) → ℤ) :
    nuOf (lamStar lam) (Fin.last m) - nuNext (nuOf (lamStar lam)) (Fin.last m) = 0 := by
  rw [nuNext_last, nuStar_apply, Fin.rev_last]
  simp

lemma expo_last {m : ℕ} (lam : Fin (m + 1) → ℤ) :
    nuOf lam (Fin.last m) - nuNext (nuOf lam) (Fin.last m) = 0 := by
  rw [nuNext_last]
  simp [PI.OddDualWeyl.nuOf]

lemma prod_minors {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (σ : Equiv.Perm (Fin (m + 1))) :
    ∏ s : Fin (m + 1), pMinor R σ (m + 1 - 1 - s.val) (by omega) ^
      (nuOf (lamStar lam) s - nuNext (nuOf (lamStar lam)) s) = pw R σ (nuOf lam) := by
  rw [PI.OddDualWeyl.pw, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, expo_star_last,
    expo_last]
  simp only [pow_zero, mul_one]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun s => ?_)
  have hr : (Fin.revPerm s : Fin m) = s.rev := rfl
  rw [hr, expo_castSucc lam hlam s]
  congr 1
  have hs := s.isLt
  exact PI.OddDualWeyl.Low.pMinor_congr σ (by simp only [Fin.val_castSucc, Fin.val_rev]; omega) _ _

lemma tele (G : ℕ → ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((n : ℤ) - 1 - j) * (G j - G (j + 1)) =
      n * G 0 - ∑ j ∈ Finset.range n, G j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ j ∈ Finset.range (n + 1), (((n + 1 : ℕ) : ℤ) - 1 - j) * (G j - G (j + 1)) =
        ((n : ℤ) - 1 - j) * (G j - G (j + 1)) + (G j - G (j + 1)) := by
      intro j _
      push_cast
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    push_cast
    ring

lemma sum_expo {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    ∑ s : Fin (m + 1), s.val * (nuOf (lamStar lam) s - nuNext (nuOf (lamStar lam)) s) = expM lam := by
  have hsplit : ∑ s : Fin (m + 1), s.val * (PI.OddDualWeyl.nuOf (PI.OddDualWeyl.lamStar lam) s -
      PI.OddDualWeyl.nuNext (PI.OddDualWeyl.nuOf (PI.OddDualWeyl.lamStar lam)) s) =
      ∑ t : Fin m, (m - 1 - t.val) * (PI.OddDualWeyl.nuOf lam t.castSucc - PI.OddDualWeyl.nuOf lam t.succ) := by
    rw [Fin.sum_univ_castSucc, expo_star_last, mul_zero, add_zero]
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun s => ?_)
    have hr : (Fin.revPerm s : Fin m) = s.rev := rfl
    rw [hr, expo_castSucc lam hlam s, nuNext_castSucc]
    congr 1
    have hs := s.isLt
    simp only [Fin.val_castSucc, Fin.val_rev]
    omega
  have hle : ∀ t : Fin m, PI.OddDualWeyl.nuOf lam t.succ ≤ PI.OddDualWeyl.nuOf lam t.castSucc :=
    nu_anti lam hlam
  have h0 : ∀ t, PI.OddDualWeyl.nuOf lam t ≤ PI.OddDualWeyl.nuOf lam 0 := fun t =>
    Int.toNat_le_toNat (by have := hlam (Fin.zero_le t); omega)
  have hlast : PI.OddDualWeyl.nuOf lam (Fin.last m) = 0 := by simp [PI.OddDualWeyl.nuOf]
  have hsum : ∑ t, PI.OddDualWeyl.nuOf lam t = ∑ t : Fin m, PI.OddDualWeyl.nuOf lam t.castSucc := by
    rw [Fin.sum_univ_castSucc, hlast, add_zero]
  have hbound : ∑ t : Fin m, PI.OddDualWeyl.nuOf lam t.castSucc ≤ m * PI.OddDualWeyl.nuOf lam 0 := by
    calc ∑ t : Fin m, PI.OddDualWeyl.nuOf lam t.castSucc ≤ ∑ _t : Fin m, PI.OddDualWeyl.nuOf lam 0 :=
          Finset.sum_le_sum fun t _ => h0 _
      _ = m * PI.OddDualWeyl.nuOf lam 0 := by simp
  let G : ℕ → ℤ := fun j => if h : j < m + 1 then (PI.OddDualWeyl.nuOf lam ⟨j, h⟩ : ℤ) else 0
  have hG : ∀ t : Fin m, G t.val = PI.OddDualWeyl.nuOf lam t.castSucc := fun t => by
    have := t.isLt
    show (if h : t.val < m + 1 then _ else _) = _
    rw [dif_pos (by omega)]
    rfl
  have hG1 : ∀ t : Fin m, G (t.val + 1) = PI.OddDualWeyl.nuOf lam t.succ := fun t => by
    have := t.isLt
    show (if h : t.val + 1 < m + 1 then _ else _) = _
    rw [dif_pos (by omega)]
    rfl
  have hG0 : G 0 = PI.OddDualWeyl.nuOf lam 0 := by simp [G]
  have key : ((∑ t : Fin m, (m - 1 - t.val) * (PI.OddDualWeyl.nuOf lam t.castSucc - PI.OddDualWeyl.nuOf lam t.succ) : ℕ) : ℤ) =
      (m : ℤ) * PI.OddDualWeyl.nuOf lam 0 - ∑ t : Fin m, (PI.OddDualWeyl.nuOf lam t.castSucc : ℤ) := by
    have e1 : ((∑ t : Fin m, (m - 1 - t.val) * (PI.OddDualWeyl.nuOf lam t.castSucc - PI.OddDualWeyl.nuOf lam t.succ) : ℕ) : ℤ) =
        ∑ j ∈ Finset.range m, ((m : ℤ) - 1 - j) * (G j - G (j + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => ((m : ℤ) - 1 - j) * (G j - G (j + 1))) m, Nat.cast_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have h1 := t.isLt
      have h2 := hle t
      have c1 : ((m - 1 - t.val : ℕ) : ℤ) = (m : ℤ) - 1 - t.val := by omega
      have c2 : ((PI.OddDualWeyl.nuOf lam t.castSucc - PI.OddDualWeyl.nuOf lam t.succ : ℕ) : ℤ) =
          (PI.OddDualWeyl.nuOf lam t.castSucc : ℤ) - PI.OddDualWeyl.nuOf lam t.succ := by omega
      rw [Nat.cast_mul, c1, c2, hG, hG1]
    rw [e1, tele, ← Fin.sum_univ_eq_sum_range G m, hG0]
    simp only [hG]
  rw [hsplit, PI.OddDualWeyl.expM, hsum, ← Nat.cast_inj (R := ℤ), key, Nat.cast_sub hbound, Nat.cast_mul, Nat.cast_sum]

lemma pm_prod {ι : Type*} (s : Finset ι) (u : ι → R) (e : ι → ℕ) (hu : ∀ i, u i = 1 ∨ u i = -1) :
    ∏ i ∈ s, u i ^ e i = 1 ∨ ∏ i ∈ s, u i ^ e i = -1 := by
  classical
  have hpow : ∀ i, u i ^ e i = 1 ∨ u i ^ e i = -1 := fun i => by
    rcases hu i with h | h
    · left
      rw [h, one_pow]
    · rw [h]
      exact neg_one_pow_eq_or R (e i)
  have hmul : ∀ a b : R, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → (a * b = 1 ∨ a * b = -1) := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  refine Finset.induction_on s ?_ ?_
  · left
    exact Finset.prod_empty
  · intro a t ha ih
    rw [Finset.prod_insert ha]
    exact hmul _ _ (hpow a) ih

lemma dualSub_C {k : ℕ} (r : R) : dualSub R k (C r) = C r := by
  simpa [MvPolynomial.algebraMap_eq] using (PI.OddDualWeyl.dualSub R k).commutes r

lemma prodStar {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (σ : Equiv.Perm (Fin (m + 1)))
    (D : Fin (m + 1) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) (u : Fin (m + 1) → R)
    (hu : ∀ s, u s = 1 ∨ u s = -1)
    (hD : ∀ s : Fin (m + 1), D s = C (u s) * (genM R (m + 1)).det ^ s.val *
      pMinor R σ (m + 1 - 1 - s.val) (by omega)) :
    ∃ U : R, (U = 1 ∨ U = -1) ∧
      ∏ s, D s ^ (nuOf (lamStar lam) s - nuNext (nuOf (lamStar lam)) s) =
        C U * (genM R (m + 1)).det ^ expM lam * pw R σ (nuOf lam) := by
  refine ⟨∏ s, u s ^ (PI.OddDualWeyl.nuOf (PI.OddDualWeyl.lamStar lam) s - PI.OddDualWeyl.nuNext (PI.OddDualWeyl.nuOf (PI.OddDualWeyl.lamStar lam)) s),
    pm_prod _ _ _ hu, ?_⟩
  simp_rw [hD, mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, sum_expo lam hlam, prod_minors lam hlam σ]
  simp only [map_prod, map_pow]

end PI.OddDualWeyl.LowA

namespace PI.OddDualWeyl

theorem highestWeightDual_of (h : JacRev) : W4hw := by
  intro R _ m lam hlam
  have hJ := fun s : Fin (m + 1) => h R (m + 1) s.val s.isLt
  choose u hu hD using hJ
  obtain ⟨U, hU, hprod⟩ := PI.OddDualWeyl.LowA.prodStar (R := R) lam hlam 1
    (fun s => dualSub R (m + 1) (pMinor R Fin.revPerm (s.val + 1) s.isLt)) u hu hD
  refine ⟨U, hU, ?_⟩
  have hC : C U * C U = (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) := by
    rw [← map_mul]
    rcases hU with rfl | rfl <;> simp
  unfold Rel low pw
  rw [map_mul, PI.OddDualWeyl.LowA.dualSub_C, map_prod]
  simp_rw [map_pow]
  rw [hprod, PI.OddDualWeyl.Low.pw_one, ← mul_assoc, ← mul_assoc, hC, one_mul]

end PI.OddDualWeyl
end
end
