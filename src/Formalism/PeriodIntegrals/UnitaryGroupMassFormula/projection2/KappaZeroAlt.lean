import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZero

section
noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

variable {k : Type} [Field k] {n c : ℕ}

private theorem symm_mem_Ufl_of_maps_Ufl {i : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)}
    (h : ∀ v ∈ PI.OneCosetSharp.Loc.Ufl k n c i, r v ∈ PI.OneCosetSharp.Loc.Ufl k n c i) {v : Fin (n + c) → k}
    (hv : v ∈ PI.OneCosetSharp.Loc.Ufl k n c i) : r.symm v ∈ PI.OneCosetSharp.Loc.Ufl k n c i := by
  have hle : (PI.OneCosetSharp.Loc.Ufl k n c i).map (r : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) ≤ PI.OneCosetSharp.Loc.Ufl k n c i := by
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  have heq : (PI.OneCosetSharp.Loc.Ufl k n c i).map (r : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) = PI.OneCosetSharp.Loc.Ufl k n c i :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq r _)
  rw [← heq] at hv
  obtain ⟨w, hw, hwv⟩ := hv
  have : r.symm v = w := by
    rw [LinearEquiv.symm_apply_eq]
    exact hwv.symm
  rw [this]
  exact hw

theorem R1cond_symm {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) : R1cond k n c r.symm := by
  obtain ⟨h1, h2, h3⟩ := hr
  refine ⟨fun i v hv => symm_mem_Ufl_of_maps_Ufl (h1 i) hv, ?_, fun i => ?_⟩
  · rw [LinearEquiv.symm_apply_eq]
    exact h2.symm
  · have hu := symm_mem_Ufl_of_maps_Ufl (h1 i) (h3 i)
    have hneg := (PI.OneCosetSharp.Loc.Ufl k n c i).neg_mem hu
    have : r.symm (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i) =
        -r.symm (r (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) := by
      rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub]
    rw [this]
    exact hneg

theorem mem_flagUnipotent {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) : r ∈ R1 k n c :=
  ⟨hr, R1cond_symm hr⟩

theorem mem_Ufl {i : ℕ} {v : Fin (n + c) → k} : v ∈ Ufl k n c i ↔ ∀ l : Fin (n + c), n + i ≤ l.1 → v l = 0 := by
  show (∀ l : Fin (n + c), l.1 ∉ {l | l < n + i} → v l = 0) ↔ _
  simp only [Set.mem_ofPred_eq, not_lt]

def XP : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if l.1 < n then LinearMap.proj l else 0

def AP : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if l.1 < n then 0 else LinearMap.proj l

theorem lowProj_apply₂ (v : Fin (n + c) → k) (l : Fin (n + c)) : (XP : (Fin (n + c) → k) →ₗ[k] _) v l = if l.1 < n then v l else 0 := by
  by_cases h : l.1 < n <;> simp [XP, h]

theorem projA_apply (v : Fin (n + c) → k) (l : Fin (n + c)) : (AP : (Fin (n + c) → k) →ₗ[k] _) v l = if l.1 < n then 0 else v l := by
  by_cases h : l.1 < n <;> simp [AP, h]

theorem lowProj_add_highProj (v : Fin (n + c) → k) : (XP : (Fin (n + c) → k) →ₗ[k] _) v + AP v = v := by
  funext l
  rw [Pi.add_apply, lowProj_apply₂, projA_apply]
  by_cases h : l.1 < n <;> simp [h]

theorem projA_inX (v : Fin n → k) : (AP : (Fin (n + c) → k) →ₗ[k] _) (inX k n c v) = 0 := by
  funext l
  rw [projA_apply]
  by_cases h : l.1 < n
  · simp [h]
  · simp [h, PI.OneCosetSharp.Loc.inX]

end PI.OneCosetSharp.W
end
end

section
noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

variable {k : Type} [Field k] {n c : ℕ}

theorem eN_apply (N i : ℕ) (l : Fin N) : eN k N i l = if l.1 = i then 1 else 0 := rfl

theorem XP_AP (w : Fin (n + c) → k) : (XP : (Fin (n + c) → k) →ₗ[k] _) (AP w) = 0 := by
  funext l
  rw [lowProj_apply₂, projA_apply]
  split_ifs <;> rfl

theorem lowProj_basisVec_of_le (q : ℕ) (hq : n ≤ q) : (XP : (Fin (n + c) → k) →ₗ[k] _) (eN k (n + c) q) = 0 := by
  funext l
  rw [lowProj_apply₂, eN_apply]
  split_ifs <;> first | rfl | omega

theorem lowProj_basisVec_of_lt (q : ℕ) (hq : q < n) : (XP : (Fin (n + c) → k) →ₗ[k] _) (eN k (n + c) q) = eN k (n + c) q := by
  funext l
  rw [lowProj_apply₂, eN_apply]
  split_ifs <;> first | rfl | omega

theorem projA_eq_self_of_projX_eq_zero {w : Fin (n + c) → k} (hw : (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0) : AP w = w := by
  have h := lowProj_add_highProj (n := n) (c := c) w
  rwa [hw, zero_add] at h

theorem fix_of_basis (g : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
    (hga : ∀ i < c, g (eN k (n + c) (n + i)) = eN k (n + c) (n + i)) (w : Fin (n + c) → k)
    (hw : (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0) : g w = w := by
  have hsum : w = ∑ l : Fin (n + c), w l • PI.OneCosetSharp.Loc.eN k (n + c) l.1 := by
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single x]
    · simp [eN_apply]
    · intro b _ hb
      have hx : x.1 ≠ b.1 := fun h => hb (Fin.ext h).symm
      simp [eN_apply, hx]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul]
  by_cases hl : l.1 < n
  · have h0 : w l = 0 := by
      have h1 := congrFun hw l
      rw [lowProj_apply₂, if_pos hl] at h1
      exact h1
    rw [h0, zero_smul, zero_smul]
  · have hlt := l.2
    have hl' : l.1 = n + (l.1 - n) := by omega
    rw [hl', hga (l.1 - n) (by omega)]

private theorem fIdx_lt_add_of_lt_add {k₀ c n p : ℕ} (hp : p < n + c) : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c := by
  unfold PI.OneCosetSharp.LocE.fIdx
  split_ifs <;> omega

private theorem fIdx_injOn_of_lt_add {k₀ c n p p' : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hp' : p' < n + c)
    (h : PI.OneCosetSharp.LocE.fIdx k₀ c n p = PI.OneCosetSharp.LocE.fIdx k₀ c n p') : p = p' := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega

private theorem mem_block_of_le_fIdx {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c)
    (h : n ≤ PI.OneCosetSharp.LocE.fIdx k₀ c n p) : k₀ ≤ p ∧ p < k₀ + c := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega

private theorem lt_or_le_of_fIdx_lt {k₀ c n p : ℕ} (h : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n) :
    p < k₀ ∨ k₀ + c ≤ p := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega

private theorem allow_of_mem_block_of_le_right {k₀ m t N c p p' : ℕ} (hcm : c + 1 < m) (hp : k₀ ≤ p)
    (hpc : p < k₀ + c) (hp' : k₀ + c ≤ p') : PI.OneCosetSharp.Allow k₀ m t N p p' := by
  unfold PI.OneCosetSharp.Allow
  split_ifs
  · omega
  · left; omega
  · left; omega

theorem gaStep : GaStep := by
  intro k _ k₀ m t j n' c n hadm g hga hfree
  obtain ⟨hk₀, -, hm4, hj1, hjm, hc, hn', hn⟩ := hadm
  generalize j * t = s at hn
  generalize (j - 1) * t = s' at hn'
  have hkn : k₀ ≤ n := by omega
  have hcm : c + 1 < m := by omega
  obtain ⟨B, hB⟩ : ∃ B : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k),
      ∀ w, B w = AP (g (XP w)) :=
    ⟨AP ∘ₗ g.toLinearMap ∘ₗ XP, fun w => rfl⟩
  have hfix : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → g w = w :=
    fix_of_basis g hga
  have hB0 : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → B w = 0 := by
    intro w hw
    rw [hB, hw]
    simp
  have hBB : ∀ w, B (B w) = 0 := fun w => hB0 _ (by rw [hB]; exact XP_AP _)
  obtain ⟨κ, hκ, hκs⟩ : ∃ κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
      (∀ w, κ w = w + B w) ∧ ∀ w, κ.symm w = w - B w := by
    refine ⟨LinearEquiv.ofLinear (LinearMap.id + B) (LinearMap.id - B) ?_ ?_, fun w => rfl, fun w => rfl⟩
    · refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_sub, hBB, add_zero]
      abel
    · refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_add, hBB, sub_zero]
      abel
  have hg : ∀ v, g v = g (XP v) + AP v := by
    intro v
    conv_lhs => rw [← lowProj_add_highProj (n := n) (c := c) v]
    rw [map_add, hfix _ (XP_AP v)]
  have hγ : ∀ v, (g * κ⁻¹) v = g (XP v) + AP v - AP (g (XP v)) := by
    intro v
    show g (κ.symm v) = _
    rw [hκs, map_sub, hfix (B v) (by rw [hB]; exact XP_AP _), hB, hg v]
  have hγl : ∀ v (l : Fin (n + c)), n ≤ l.1 → (g * κ⁻¹) v l = v l := by
    intro v l hl
    rw [hγ]
    simp only [Pi.sub_apply, Pi.add_apply, projA_apply, if_neg (not_lt.mpr hl)]
    ring
  have hγfix : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → (g * κ⁻¹) w = w := by
    intro w hw
    rw [hγ, hw]
    simp [projA_eq_self_of_projX_eq_zero hw]
  have hU : PI.OneCosetSharp.Loc.R1cond k n c (g * κ⁻¹) := by
    refine ⟨fun i v hv => ?_, hγfix _ (lowProj_basisVec_of_le n le_rfl), fun i => ?_⟩
    · rw [mem_Ufl] at hv ⊢
      intro l hl
      rw [hγl v l (by omega)]
      exact hv l hl
    · rw [hγfix _ (lowProj_basisVec_of_le (n + i) (Nat.le_add_right n i)), sub_self]
      exact Submodule.zero_mem _
  have hentry : ∀ p p' (hp : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c),
      PI.OneCosetSharp.ent k₀ c n c n κ.toLinearMap p p' =
        (PI.OneCosetSharp.Loc.eN k (n + c) (PI.OneCosetSharp.LocE.fIdx k₀ c n p') + B (PI.OneCosetSharp.Loc.eN k (n + c) (PI.OneCosetSharp.LocE.fIdx k₀ c n p'))) ⟨_, hp⟩ := by
    intro p p' hp
    simp only [PI.OneCosetSharp.ent, PI.OneCosetSharp.Loc.atN, dif_pos hp, LinearEquiv.coe_coe, hκ]
  have hBq : ∀ q (hq : q < n + c), B (PI.OneCosetSharp.Loc.eN k (n + c) q) ⟨q, hq⟩ = 0 := by
    intro q hq
    by_cases h : q < n
    · rw [hB, projA_apply]
      exact if_pos h
    · rw [hB0 _ (lowProj_basisVec_of_le q (not_lt.mp h))]
      rfl
  refine ⟨g * κ⁻¹, mem_flagUnipotent hU, κ, ⟨fun p' hp' => ?_, fun p p' hp hp' hne hent => ?_⟩, by simp⟩
  · have hq := fIdx_lt_add_of_lt_add (k₀ := k₀) (show p' < n + c by omega)
    rw [hentry p' p' hq, Pi.add_apply, hBq _ hq, add_zero, eN_apply]
    exact if_pos rfl
  · have hq := fIdx_lt_add_of_lt_add (k₀ := k₀) hp
    have hqq : PI.OneCosetSharp.LocE.fIdx k₀ c n p ≠ PI.OneCosetSharp.LocE.fIdx k₀ c n p' := fun h => hne (fIdx_injOn_of_lt_add hkn hp hp' h)
    rw [hentry p p' hq, Pi.add_apply, eN_apply, Fin.val_mk, if_neg hqq, zero_add] at hent
    by_cases hq'n : PI.OneCosetSharp.LocE.fIdx k₀ c n p' < n
    · rw [hB, lowProj_basisVec_of_lt _ hq'n] at hent
      rcases lt_or_le_of_fIdx_lt hq'n with h | h
      · obtain ⟨v, hv⟩ := hfree p' (by omega) (Or.inl h)
        rw [hv, projA_inX] at hent
        exact (hent rfl).elim
      · rw [projA_apply] at hent
        have hpn : n ≤ PI.OneCosetSharp.LocE.fIdx k₀ c n p := by
          by_contra h'
          exact hent (if_pos (not_le.mp h'))
        obtain ⟨hp1, hp2⟩ := mem_block_of_le_fIdx hkn hp hpn
        exact allow_of_mem_block_of_le_right hcm hp1 hp2 h
    · rw [hB0 _ (lowProj_basisVec_of_le _ (not_lt.mp hq'n))] at hent
      exact (hent rfl).elim

end PI.OneCosetSharp.W
end
end

section
noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

variable {k : Type} [Field k] {n' c n : ℕ}

theorem embedMatrix_basisVec_apply_of_not_free (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (tt : FC n' (c + 1) n c → k) (i : ℕ) (hi : i < c)
    (l : Fin (n + c)) (hf : ¬ IsFree n' n c l.1 (n' + i)) :
    xx1 xj tt (eN k (n' + (c + 1)) (n' + i)) l = if l.1 = n + i then 1 else 0 := by
  have hs : n' + i < n' + (c + 1) := by omega
  have he : eN k (n' + (c + 1)) (n' + i) = Pi.single (⟨n' + i, hs⟩ : Fin (n' + (c + 1))) 1 := by
    funext s
    unfold eN
    by_cases h : (s : ℕ) = n' + i
    · have : s = ⟨n' + i, hs⟩ := Fin.ext h
      subst this
      simp
    · have : s ≠ ⟨n' + i, hs⟩ := fun e => h (by rw [e])
      simp [h, this]
  have key : ∀ (A : Matrix (Fin (n + c)) (Fin (n' + (c + 1))) k) (j : Fin (n' + (c + 1))),
      Matrix.toLin' A (Pi.single j 1) l = A l j := by
    intro A j
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    rfl
  rw [he]
  unfold xx1
  rw [key, Matrix.of_apply,
    dif_neg (show ¬ IsFree n' n c l.1 (⟨n' + i, hs⟩ : Fin (n' + (c + 1))).1 from hf),
    dif_neg (show ¬ ((⟨n' + i, hs⟩ : Fin (n' + (c + 1))).1 < n') by show ¬ (n' + i < n'); omega)]
  show (if l.1 = n + (n' + i - n') then (1 : k) else 0) = _
  rw [Nat.add_sub_cancel_left]

theorem nElem : NElem := by
  intro k _ n' c n xj tt
  classical

  have heN : ∀ (N j : ℕ) (hj : j < N), eN k N j = Pi.single (⟨j, hj⟩ : Fin N) 1 := by
    intro N j hj
    funext s
    unfold eN
    by_cases h : (s : ℕ) = j
    · have : s = ⟨j, hj⟩ := Fin.ext h
      subst this
      simp
    · have : s ≠ ⟨j, hj⟩ := fun e => h (by rw [e])
      simp [h, this]
  have hnf : ∀ (l : Fin (n + c)) (i : ℕ), i < c → (i = 0 ∨ n + i ≤ l.1) →
      ¬ IsFree n' n c l.1 (n' + i) := by
    intro l i hi h
    unfold IsFree
    omega

  let M : Matrix (Fin (n + c)) (Fin (n + c)) k := Matrix.of fun l s =>
    if s.1 < n then (if l = s then 1 else 0)
    else xx1 xj tt (eN k (n' + (c + 1)) (n' + (s.1 - n))) l
  have hM_lt : ∀ l s : Fin (n + c), s.1 < n → M l s = if l = s then 1 else 0 := by
    intro l s hs
    simp [M, hs]
  have hM_ge : ∀ (l : Fin (n + c)) (j : ℕ) (hj : j < n + c), ¬ j < n →
      M l ⟨j, hj⟩ = xx1 xj tt (eN k (n' + (c + 1)) (n' + (j - n))) l := by
    intro l j hj hn
    simp [M, hn]
  have hT : ∀ l s : Fin (n + c), s < l → M l s = 0 := by
    intro l s hsl
    have hsl' : s.1 < l.1 := hsl
    by_cases hs : s.1 < n
    · rw [hM_lt l s hs, if_neg (fun h => by rw [h] at hsl'; exact lt_irrefl _ hsl')]
    · have hsc := s.2
      rw [show s = ⟨s.1, s.2⟩ from rfl, hM_ge l s.1 s.2 hs,
        embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) l (hnf l (s.1 - n) (by omega) (Or.inr (by omega))),
        if_neg (by omega)]
  have hD : ∀ s : Fin (n + c), M s s = 1 := by
    intro s
    by_cases hs : s.1 < n
    · rw [hM_lt s s hs, if_pos rfl]
    · have hsc := s.2
      rw [show s = ⟨s.1, s.2⟩ from rfl, hM_ge _ s.1 s.2 hs,
        embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) _ (hnf _ (s.1 - n) (by omega) (Or.inr (by simp; omega))),
        if_pos (by simp; omega)]
  have hUT : M.BlockTriangular id := fun i j hij => hT i j hij
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular hUT]
    simp [hD]
  let hinv : Invertible M := Matrix.invertibleOfIsUnitDet M hdet
  let ν := M.toLinearEquiv' hinv
  have hν : ∀ x, ν x = M.mulVec x := by
    intro x
    show (↑(M.toLinearEquiv' hinv) : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) x = _
    rw [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  have hcol : ∀ (j : ℕ) (hj : j < n + c), M.mulVec (eN k (n + c) j) = fun l => M l ⟨j, hj⟩ := by
    intro j hj
    rw [heN _ j hj, Matrix.mulVec_single_one]
    rfl
  have hνcol : ∀ i, i < c → ν (eN k (n + c) (n + i)) = xx1 xj tt (eN k (n' + (c + 1)) (n' + i)) := by
    intro i hi
    rw [hν, hcol (n + i) (by omega)]
    funext l
    rw [hM_ge l (n + i) (by omega) (by omega), Nat.add_sub_cancel_left]
  have hinX : ∀ (v : Fin n → k) (s : Fin (n + c)), ¬ s.1 < n → inX k n c v s = 0 := by
    intro v s hs
    simp [inX, hs]
  have hzero : ∀ i, ¬ i < c → eN k (n + c) (n + i) = 0 := by
    intro i hi
    funext l
    unfold eN
    split_ifs with h
    · have := l.2
      omega
    · rfl
  refine ⟨ν, mem_flagUnipotent ⟨?_, ?_, ?_⟩, ?_, hνcol⟩
  · intro i v hv
    have hv' : ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → v l = 0 := hv
    show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → (ν v) l = 0
    intro l hl
    have hl' : n + i ≤ l.1 := by simpa using hl
    rw [hν]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s.1 < n + i
    · rw [hT l s (show s.1 < l.1 by omega), zero_mul]
    · rw [hv' s (by simpa using hs), mul_zero]
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · rw [show eN k (n + c) n = 0 from by simpa using hzero 0 (by omega), map_zero]
    · have h0 := hνcol 0 hc
      have e1 : xx1 xj tt (eN k (n' + (c + 1)) (n' + 0)) = eN k (n + c) (n + 0) := by
        funext l
        rw [embedMatrix_basisVec_apply_of_not_free xj tt 0 hc l (hnf l 0 hc (Or.inl rfl))]
        rfl
      exact h0.trans e1
  · intro i
    show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) →
      (ν (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) l = 0
    intro l hl
    have hl' : n + i ≤ l.1 := by simpa using hl
    by_cases hi : i < c
    · rw [hνcol i hi, Pi.sub_apply, embedMatrix_basisVec_apply_of_not_free xj tt i hi l (hnf l i hi (Or.inr hl'))]
      show (if l.1 = n + i then (1 : k) else 0) - (if l.1 = n + i then 1 else 0) = 0
      exact sub_self _
    · rw [hzero i hi, map_zero, sub_zero]
      rfl
  · intro v
    rw [hν]
    funext l
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single l]
    · rw [hD l, one_mul]
    · intro s _ hsl
      by_cases hs : s.1 < n
      · rw [hM_lt l s hs, if_neg (fun h => hsl h.symm), zero_mul]
      · rw [hinX v s hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h

end PI.OneCosetSharp.W
end
end

section
open PI.OneCosetSharp PI.OneCosetSharp.Loc PI.OneCosetSharp.LocE

noncomputable section

namespace PI.OneCosetSharp.W.P2

def S (k₀ m t N p q : ℕ) : Prop := p = q ∨ Allow k₀ m t N p q

theorem allow_col_lt {k₀ m t N p q : ℕ} (hq : q < k₀ + m - 1) (h : Allow k₀ m t N p q) : p < k₀ + m - 1 := by
  unfold Allow at h
  split_ifs at h <;> omega

theorem S_trans {k₀ m t N p q s : ℕ} (h1 : S k₀ m t N p q) (h2 : S k₀ m t N q s) : S k₀ m t N p s := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  by_cases hps : p = s
  · exact Or.inl hps
  right
  unfold Allow at h1 h2 ⊢
  generalize (p - (k₀ + m - 1)) / t = bp at *
  generalize (q - (k₀ + m - 1)) / t = bq at *
  generalize (s - (k₀ + m - 1)) / t = bs at *
  split_ifs at h1 h2 ⊢ <;> omega

def φ (k₀ m p : ℕ) : ℕ := if p < k₀ then m + p else if p < k₀ + (m / 2 - 1) then p - k₀ else p + 2 * m + k₀

theorem allow_lt_φ {k₀ m t N p q : ℕ} (hq : q < k₀ + m - 1) (h : Allow k₀ m t N p q) : φ k₀ m p < φ k₀ m q := by
  unfold Allow at h
  unfold φ
  split_ifs at h ⊢ <;> omega

theorem S_antisymm {k₀ m t N p q : ℕ} (hp : p < k₀ + m - 1) (h1 : S k₀ m t N p q) (h2 : S k₀ m t N q p) : p = q := by
  rcases h1 with h1 | h1
  · exact h1
  rcases h2 with h2 | h2
  · exact h2.symm
  have hq := allow_col_lt hp h2
  have a := allow_lt_φ hq h1
  have b := allow_lt_φ hp h2
  omega

variable {k : Type} [Field k]

def alg (k₀ m t b : ℕ) : Submodule k (Matrix (Fin b) (Fin b) k) where
  carrier := {A | ∀ p q, A p q ≠ 0 → S k₀ m t b p.1 q.1}
  add_mem' := by
    intro A B hA hB p q h
    by_contra hs
    apply h
    simp only [Matrix.add_apply]
    rw [not_imp_comm.1 (hA p q) hs, not_imp_comm.1 (hB p q) hs, add_zero]
  zero_mem' := fun _ _ h => absurd rfl h
  smul_mem' := by
    intro a A hA p q h
    by_contra hs
    apply h
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [not_imp_comm.1 (hA p q) hs, mul_zero]

variable {k₀ m t b : ℕ}

theorem mem_alg {A : Matrix (Fin b) (Fin b) k} : A ∈ alg (k := k) k₀ m t b ↔ ∀ p q, A p q ≠ 0 → S k₀ m t b p.1 q.1 :=
  Iff.rfl

theorem alg_one : (1 : Matrix (Fin b) (Fin b) k) ∈ alg (k := k) k₀ m t b := by
  intro p q h
  left
  rw [Matrix.one_apply] at h
  split_ifs at h with hpq
  · exact congrArg Fin.val hpq
  · exact absurd rfl h

theorem alg_mul {A B : Matrix (Fin b) (Fin b) k} (hA : A ∈ alg (k := k) k₀ m t b) (hB : B ∈ alg (k := k) k₀ m t b) :
    A * B ∈ alg (k := k) k₀ m t b := by
  intro p q h
  rw [Matrix.mul_apply] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact S_trans (hA p s (left_ne_zero_of_mul hs)) (hB s q (right_ne_zero_of_mul hs))

theorem alg_inv {A B : Matrix (Fin b) (Fin b) k} (hA : A ∈ alg (k := k) k₀ m t b) (hBA : B * A = 1) :
    B ∈ alg (k := k) k₀ m t b := by
  let f : alg (k := k) k₀ m t b →ₗ[k] alg (k := k) k₀ m t b :=
    (LinearMap.mulLeft k A).restrict (fun X hX => alg_mul hA hX)
  have hf : ∀ X : alg (k := k) k₀ m t b, (f X).1 = A * X.1 := fun X => rfl
  have hinj : Function.Injective f := by
    intro X Y hXY
    have h1 : A * X.1 = A * Y.1 := by rw [← hf, ← hf, hXY]
    apply Subtype.ext
    have h2 := congrArg (B * ·) h1
    simpa only [← Matrix.mul_assoc, hBA, Matrix.one_mul] using h2
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨1, alg_one⟩
  have hAX : A * X.1 = 1 := by rw [← hf, hX]
  have : B = X.1 := by
    calc B = B * (A * X.1) := by rw [hAX, Matrix.mul_one]
      _ = X.1 := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  rw [this]
  exact X.2

theorem alg_diag {A B : Matrix (Fin b) (Fin b) k} (hA : A ∈ alg (k := k) k₀ m t b) (hB : B ∈ alg (k := k) k₀ m t b)
    (p : Fin b) (hp : p.1 < k₀ + m - 1) : (A * B) p p = A p p * B p p := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · intro s _ hs
    by_contra h
    exact hs (Fin.ext (S_antisymm hp (hA p s (left_ne_zero_of_mul h)) (hB s p (right_ne_zero_of_mul h)))).symm
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : fIdx k₀ c n p < n + c := by
  unfold fIdx
  split_ifs <;> omega

theorem fIdx_inj {k₀ c n p q : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hq : q < n + c)
    (h : fIdx k₀ c n p = fIdx k₀ c n q) : p = q := by
  unfold fIdx at h
  split_ifs at h <;> omega

def fe (k₀ c n : ℕ) (hk : k₀ ≤ n) : Fin (n + c) ≃ Fin (n + c) :=
  Equiv.ofBijective (fun p => ⟨fIdx k₀ c n p.1, fIdx_lt hk p.2⟩)
    (Finite.injective_iff_bijective.1 fun p q h => Fin.ext (fIdx_inj hk p.2 q.2 (congrArg Fin.val h)))

def Pm {c n : ℕ} (k₀ : ℕ) (hk : k₀ ≤ n) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Matrix (Fin (n + c)) (Fin (n + c)) k :=
  (LinearMap.toMatrix' κ.toLinearMap).submatrix (fe k₀ c n hk) (fe k₀ c n hk)

theorem ent_eq {c n : ℕ} (hk : k₀ ≤ n) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (p q : Fin (n + c)) :
    ent k₀ c n c n κ.toLinearMap p.1 q.1 = Pm k₀ hk κ p q := by
  have e : eN k (n + c) (fIdx k₀ c n q.1) = Pi.single (fe k₀ c n hk q) (1 : k) := by
    funext j'
    simp only [eN, Pi.single_apply, fe, Equiv.ofBijective_apply, Fin.ext_iff]
  simp only [Pm, Matrix.submatrix_apply, LinearMap.toMatrix'_apply, ent, atN, dif_pos (fIdx_lt hk p.2), e]
  rfl

theorem Pm_mul {c n : ℕ} (hk : k₀ ≤ n) (κ₁ κ₂ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Pm k₀ hk (κ₁ * κ₂) = Pm k₀ hk κ₁ * Pm k₀ hk κ₂ := by
  have e : (κ₁ * κ₂).toLinearMap = κ₁.toLinearMap ∘ₗ κ₂.toLinearMap := LinearMap.ext fun _ => rfl
  rw [Pm, Pm, Pm, e, LinearMap.toMatrix'_comp, Matrix.submatrix_mul_equiv]

theorem Pm_one {c n : ℕ} (hk : k₀ ≤ n) : Pm (k := k) (c := c) (n := n) k₀ hk 1 = 1 := by
  have e : (1 : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)).toLinearMap = LinearMap.id := LinearMap.ext fun _ => rfl
  rw [Pm, e, LinearMap.toMatrix'_id, Matrix.submatrix_one_equiv]

theorem injs_iff {c n : ℕ} (hk : k₀ ≤ n) (hr : k₀ + m - 1 ≤ n + c) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    InJS k₀ m t c n κ ↔ Pm k₀ hk κ ∈ alg (k := k) k₀ m t (n + c) ∧ ∀ p : Fin (n + c), p.1 < k₀ + m - 1 → Pm k₀ hk κ p p = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p q h => ?_, fun p hp => ?_⟩
    · by_cases hpq : p = q
      · exact Or.inl (congrArg Fin.val hpq)
      · right
        refine h2 p.1 q.1 p.2 q.2 (fun e => hpq (Fin.ext e)) ?_
        rwa [ent_eq hk]
    · rw [← ent_eq hk]
      exact h1 p.1 hp
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => ?_, fun p q hp hq hpq h => ?_⟩
    · have := h2 ⟨p, by omega⟩ hp
      rwa [← ent_eq hk] at this
    · rw [show p = (⟨p, hp⟩ : Fin (n + c)).1 from rfl, show q = (⟨q, hq⟩ : Fin (n + c)).1 from rfl, ent_eq hk] at h
      rcases h1 _ _ h with h | h
      · exact absurd h hpq
      · exact h

theorem nums_le {k₀ m t j n' c n : ℕ} (h : Nums k₀ m t j n' c n) : k₀ ≤ n ∧ k₀ + m - 1 ≤ n + c := by
  obtain ⟨h1, -, h3, h4, h5, h6, -, h8⟩ := h
  generalize j * t = J at h8
  omega

end PI.OneCosetSharp.W.P2

namespace PI.OneCosetSharp.W

open P2 in
theorem patClosed : PatClosed := by
  intro k _ k₀ m t j n' c n hN κ₁ κ₂ h₁ h₂
  obtain ⟨hk, hr⟩ := nums_le hN
  rw [injs_iff hk hr] at h₁ h₂
  refine ⟨?_, ?_⟩
  · rw [injs_iff hk hr, Pm_mul]
    refine ⟨alg_mul h₁.1 h₂.1, fun p hp => ?_⟩
    rw [alg_diag h₁.1 h₂.1 p hp, h₁.2 p hp, h₂.2 p hp, mul_one]
  · have hBA : Pm k₀ hk κ₁⁻¹ * Pm k₀ hk κ₁ = 1 := by rw [← Pm_mul, inv_mul_cancel, Pm_one]
    have hB := alg_inv h₁.1 hBA
    rw [injs_iff hk hr]
    refine ⟨hB, fun p hp => ?_⟩
    have := congrFun (congrFun hBA p) p
    rw [alg_diag hB h₁.1 p hp, h₁.2 p hp, mul_one, Matrix.one_apply_eq] at this
    exact this

end PI.OneCosetSharp.W
end
end

section
noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

private theorem det_eq_det_castLE_of_cols_eq_one {k : Type} [Field k] {a t N : ℕ} (hN : a + t = N)
    (K : Matrix (Fin N) (Fin N) k) (h0 : ∀ p q : Fin N, a ≤ q.1 → K p q = if p = q then 1 else 0) :
    K.det = (Matrix.of fun s s' : Fin a =>
      K (Fin.castLE (Nat.le.intro hN) s) (Fin.castLE (Nat.le.intro hN) s')).det := by
  subst hN
  have hK : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm K =
      Matrix.fromBlocks (Matrix.of fun s s' : Fin a => K (Fin.castAdd t s) (Fin.castAdd t s'))
        0 (Matrix.of fun (s : Fin t) (s' : Fin a) => K (Fin.natAdd a s) (Fin.castAdd t s')) 1 := by
    ext (s | s) (s' | s')
    · rfl
    · show K (Fin.castAdd t s) (Fin.natAdd a s') = 0
      rw [h0 (Fin.castAdd t s) (Fin.natAdd a s') (by simp), if_neg]
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rfl
    · show K (Fin.natAdd a s) (Fin.natAdd a s') = (1 : Matrix (Fin t) (Fin t) k) s s'
      rw [h0 (Fin.natAdd a s) (Fin.natAdd a s') (by simp), Matrix.one_apply]
      by_cases h : s = s'
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro h'
        apply h
        have := congrArg Fin.val h'
        simp only [Fin.val_natAdd] at this
        exact Fin.ext (by omega)
  rw [← Matrix.det_reindex_self finSumFinEquiv.symm K, hK, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, mul_one]
  rfl

private theorem allow_mono {k₀ m t a b p q : ℕ} (hab : a ≤ b) (h : PI.OneCosetSharp.Allow k₀ m t a p q) :
    PI.OneCosetSharp.Allow k₀ m t b p q := by
  unfold PI.OneCosetSharp.Allow at h ⊢
  split_ifs at h ⊢
  · exact h
  · exact h
  · rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨lt_of_lt_of_le h1 hab, h2⟩

theorem kappaZero : KappaZero := by
  intro k inst ψ₀ χ k₀ m t j n' c n hadm y hy
  obtain ⟨hk, hr⟩ := PI.OneCosetSharp.W.P2.nums_le hadm
  obtain ⟨-, -, -, hj1, -, -, hdom, hcod⟩ := hadm
  have hN : k₀ + m - 1 + (j - 1) * t + t = n + c := by
    rw [hcod]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    generalize k₀ + m - 1 = r
    ring
  have key : (∀ p', p' < k₀ + m - 1 → PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p' p' = 1) ∧
      (∀ p p', p < n + c → p' < k₀ + m - 1 + (j - 1) * t → p ≠ p' → PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p p' ≠ 0 →
        PI.OneCosetSharp.Allow k₀ m t (k₀ + m - 1 + (j - 1) * t) p p') ∧
      (Matrix.of fun s s' : Fin (k₀ + m - 1 + (j - 1) * t) =>
        PI.OneCosetSharp.ent k₀ (c + 1) n' c n y s.1 s'.1).det ≠ 0 := by
    simp only [PI.OneCosetSharp.PhiS] at hy
    split_ifs at hy with hcond
    · refine ⟨hcond.1, hcond.2, fun hdet => hy ?_⟩
      rw [hdet]
      simp [PI.OneCosetSharp.chiV]
    · exact absurd rfl hy
  have hcoord : ∀ (v : Fin (n + c) → k) (l : Fin (n + c)), PI.OneCosetSharp.Loc.atN v l.1 = v l := fun v l => by
    simp only [PI.OneCosetSharp.Loc.atN, dif_pos l.2, Fin.eta]
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Fin (n + c)) (Fin (n + c)) k, ∀ p q, K p q =
      if q.1 < k₀ + m - 1 + (j - 1) * t then PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p.1 q.1 else if p = q then 1 else 0 :=
    ⟨Matrix.of fun p q => if q.1 < k₀ + m - 1 + (j - 1) * t then PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p.1 q.1
      else if p = q then 1 else 0, fun _ _ => rfl⟩
  have hdetK : K.det ≠ 0 := by
    rw [det_eq_det_castLE_of_cols_eq_one hN K (fun p q hq => by rw [hK, if_neg (not_lt.mpr hq)])]
    refine ne_of_eq_of_ne ?_ key.2.2
    congr 1
    ext s s'
    simp only [Matrix.of_apply]
    rw [hK, if_pos] <;> first | rfl | exact s'.2
  have hA : IsUnit (K.submatrix (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm
      (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm).det := by
    rw [Matrix.det_submatrix_equiv_self]
    exact isUnit_iff_ne_zero.mpr hdetK
  obtain ⟨κ, hκ⟩ : ∃ κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k), κ.toLinearMap =
      Matrix.toLin' (K.submatrix (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm) :=
    ⟨Matrix.toLinearEquiv' _ (Matrix.invertibleOfIsUnitDet _ hA), rfl⟩
  have hperm : PI.OneCosetSharp.W.P2.Pm k₀ hk κ = K := by
    unfold PI.OneCosetSharp.W.P2.Pm
    rw [hκ, LinearMap.toMatrix'_toLin']
    ext p q
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  refine ⟨κ, ?_, ?_⟩
  · rw [PI.OneCosetSharp.W.P2.injs_iff hk hr κ, hperm, PI.OneCosetSharp.W.P2.mem_alg]
    refine ⟨fun p q hpq => ?_, fun p hp => ?_⟩
    · by_cases hpq' : p = q
      · exact Or.inl (congrArg Fin.val hpq')
      · refine Or.inr ?_
        have hne : p.1 ≠ q.1 := fun h => hpq' (Fin.ext h)
        by_cases hq : q.1 < k₀ + m - 1 + (j - 1) * t
        · rw [hK, if_pos hq] at hpq
          exact allow_mono (Nat.le.intro hN) (key.2.1 p.1 q.1 p.2 hq hne hpq)
        · rw [hK, if_neg hq, if_neg hpq'] at hpq
          exact absurd rfl hpq
    · have hpa : p.1 < k₀ + m - 1 + (j - 1) * t := by omega
      rw [hK, if_pos hpa]
      exact key.1 p.1 hp
  · intro p hp
    have hpa : p < k₀ + m - 1 + (j - 1) * t := by omega
    have hpN : p < n + c := by omega
    funext l
    have hl : PI.OneCosetSharp.LocE.fIdx k₀ c n ((PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm l).1 = l.1 :=
      congrArg Fin.val ((PI.OneCosetSharp.W.P2.fe k₀ c n hk).apply_symm_apply l)
    have e1 := PI.OneCosetSharp.W.P2.ent_eq hk κ ((PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm l) ⟨p, hpN⟩
    rw [hperm, hK, if_pos hpa] at e1
    unfold PI.OneCosetSharp.ent at e1
    rw [hl, hcoord, hcoord] at e1
    exact e1

end PI.OneCosetSharp.W
end
end
