import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.XLeOrthXplus
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Skeleton

section
noncomputable section

open scoped Classical

namespace PI.ScalarPairDr.W

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E]

section Core

variable {S : HSpace E} (Λ : Submodule (𝓞 E) S.V) {r : ℕ} {T T' : E}

theorem UUE_eq (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z)
    (hX : Xsp F ≤ spanE S (XLam Λ F)) (hX' : Xsp F' ≤ spanE S (XLam Λ F')) :
    UUE Λ F F' = Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)) := by
  have hfv : ∀ i, F.fl.fvec i ∈ Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)) :=
    fun i => Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hfv' : ∀ i, F'.fl.fvec i ∈ Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)) :=
    fun i => Submodule.subset_span ⟨Sum.inr i, rfl⟩
  have hXF : Xsp F ≤ Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)) := by
    unfold Xsp Formalism.MainNotions.S.FlagG.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have he : F.fl.fvec (Fin.castSucc a) = F.fl.e a := by simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [← he]
    exact hfv _
  have hXF' : Xsp F' ≤ Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)) := by
    unfold Xsp Formalism.MainNotions.S.FlagG.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have he : F'.fl.fvec (Fin.castSucc a) = F'.fl.e a := by simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [← he]
    exact hfv' _
  have hzF : F.zt ∈ Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)) := by
    have he : F.fl.fvec (Fin.last r) = F.fl.z := by simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [hz, ← he]
    exact hfv _
  have hzF' : F'.zt ∈ Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)) := by
    have he : F'.fl.fvec (Fin.last r) = F'.fl.z := by simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [hz', ← he]
    exact hfv' _
  apply le_antisymm
  · unfold UUE spanE
    rw [Submodule.span_le]
    intro u hu
    change u ∈ UU Λ F F' at hu
    unfold UU at hu
    obtain ⟨y1, hy1, d, hd, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨y2, hy2, c, hc, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy2
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
    obtain ⟨t', rfl⟩ := Submodule.mem_span_singleton.mp hd
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · exact hXF (show a ∈ Λ ∧ a ∈ Xsp F from ha).2
    · exact Submodule.smul_of_tower_mem _ t hzF
    · exact hXF' (show c ∈ Λ ∧ c ∈ Xsp F' from hc).2
    · exact Submodule.smul_of_tower_mem _ t' hzF'
  · rw [Submodule.span_le]
    have hXU : ∀ v, v ∈ XLam Λ F → v ∈ UU Λ F F' := fun v hv => by
      unfold UU
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left hv))
    have hXU' : ∀ v, v ∈ XLam Λ F' → v ∈ UU Λ F F' := fun v hv => by
      unfold UU
      exact Submodule.mem_sup_left (Submodule.mem_sup_right hv)
    have hS : spanE S (XLam Λ F) ≤ UUE Λ F F' := by
      unfold UUE spanE
      exact Submodule.span_mono (fun v hv => hXU v hv)
    have hS' : spanE S (XLam Λ F') ≤ UUE Λ F F' := by
      unfold UUE spanE
      exact Submodule.span_mono (fun v hv => hXU' v hv)
    have hzU : F.zt ∈ UUE Λ F F' := by
      unfold UUE spanE
      apply Submodule.subset_span
      change F.zt ∈ UU Λ F F'
      unfold UU
      exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
    have hzU' : F'.zt ∈ UUE Λ F F' := by
      unfold UUE spanE
      apply Submodule.subset_span
      change F'.zt ∈ UU Λ F F'
      unfold UU
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    rintro _ ⟨i, rfl⟩
    rcases i with i | i
    · refine Fin.lastCases ?_ (fun a => ?_) i
      · simp only [Sum.elim_inl, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
        rw [← hz]
        exact hzU
      · simp only [Sum.elim_inl, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
        exact hS (hX (show F.fl.e a ∈ Xsp F by
          unfold Xsp Formalism.MainNotions.S.FlagG.X
          exact Submodule.subset_span ⟨a, rfl⟩))
    · refine Fin.lastCases ?_ (fun a => ?_) i
      · simp only [Sum.elim_inr, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
        rw [← hz']
        exact hzU'
      · simp only [Sum.elim_inr, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
        exact hS' (hX' (show F'.fl.e a ∈ Xsp F' by
          unfold Xsp Formalism.MainNotions.S.FlagG.X
          exact Submodule.subset_span ⟨a, rfl⟩))

theorem mem_ThPairs (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V) (p : S.V × S.V) :
    p ∈ ThPairs Λ F F' F'' β ↔ p.1 ∈ Hp Λ F F' ∧ p.2 ∈ Hp Λ F F'' ∧ p.1 - p.2 ∈ Xsp F ∧
      β p.1 - p.2 ∈ Xsp F'' := by
  unfold ThPairs
  simp only [Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, and_assoc]

theorem core (k : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hz'' : F''.zt = F''.fl.z)
    (hX : Xsp F ≤ spanE S (XLam Λ F)) (hX' : Xsp F' ≤ spanE S (XLam Λ F'))
    (hX'' : Xsp F'' ≤ spanE S (XLam Λ F''))
    (hn : finrank E S.V = k + 2 * r + 1) (hT : T ≠ 0)
    (hG' : Gval F F' ≠ 0) (hG'' : Gval F F'' ≠ 0)
    (hs : s0 Λ F F' F'' β k = 1) (hsc : IsScalar Λ F F' F'' β) :
    Dr F F' = 0 ↔ Dr F F'' = 0 := by
  have hU1 := UUE_eq Λ F F' hz hz' hX hX'
  have hU2 := UUE_eq Λ F F'' hz hz'' hX hX''
  have hd1 : finrank E (UUE Λ F F') = 2 * r + 2 := by
    rw [hU1, finrank_span_eq_card (PI.PairCorankPos.W.linIndep F.fl F'.fl hG')]
    simp
    omega
  have hd2 : finrank E (UUE Λ F F'') = 2 * r + 2 := by
    rw [hU2, finrank_span_eq_card (PI.PairCorankPos.W.linIndep F.fl F''.fl hG'')]
    simp
    omega
  have hH1 : finrank E (Hp Λ F F') + 1 = k := by
    have := finrank_orth S (UUE Λ F F')
    rw [Hp]
    omega
  have hH2 : finrank E (Hp Λ F F'') + 1 = k := by
    have := finrank_orth S (UUE Λ F F'')
    rw [Hp]
    omega
  have hTh : finrank E (Th Λ F F' F'' β) + 1 = k := by
    unfold s0 at hs
    omega

  have hThle : Th Λ F F' F'' β ≤ Hp Λ F F' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).1
  have hTheq : Th Λ F F' F'' β = Hp Λ F F' :=
    Submodule.eq_of_le_of_finrank_eq hThle (by omega)

  have hTh''le : Th'' Λ F F' F'' β ≤ Hp Λ F F'' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).2.1
  have hTh''eq : Th'' Λ F F' F'' β = Hp Λ F F'' := by
    refine Submodule.eq_of_le_of_finrank_eq hTh''le ?_
    let f := (LinearMap.snd E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype
    have hker : LinearMap.ker f = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro p hp
      have hm := (mem_ThPairs Λ F F' F'' β p.1).1 p.2
      have h2 : p.1.2 = 0 := hp
      have hx1 : p.1.1 ∈ F.fl.X := by
        have := hm.2.2.1
        rwa [h2, sub_zero] at this
      have h1 : p.1.1 = 0 := by
        refine eq_zero_of_orth F.fl F'.fl hG' hx1 fun b => ?_
        have hm1 := hm.1
        rw [Hp, mem_orth] at hm1
        exact hm1 _ (by rw [hU1]; exact Submodule.subset_span ⟨Sum.inr b, rfl⟩)
      exact Subtype.ext (Prod.ext h1 h2)
    have hrange : LinearMap.range f = Th'' Λ F F' F'' β := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    rw [hker, hrange, finrank_bot] at h1
    have h2 : finrank E (Th Λ F F' F'' β) ≤ finrank E (ThPairs Λ F F' F'' β) :=
      Submodule.finrank_map_le _ _
    have h3 := Submodule.finrank_mono hTh''le
    omega

  have key : ∀ y ∈ Ylift Λ F F', y ∈ Ylift Λ F F'' →
      (SgRel F F' y 0 1 0 ↔ SgRel F F'' y 0 1 0) := fun y h1 h2 =>
    hsc y h1 y h2 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) (by simp)
      (by simp) 1 0
  have hzX : ∀ x ∈ Xsp F, S.hT F.fl.z x = 0 := fun x hx =>
    (mem_orth S).1 (X_le_orth_Xplus F.fl hx) _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have heX : ∀ x ∈ Xsp F, ∀ a, S.hT (F.fl.e a) x = 0 := fun x hx a =>
    (mem_orth S).1 (X_le_orth_Xplus F.fl hx) _ (Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩))

  have hyo : ∀ b : S.V, (∀ a, S.hT (F.fl.e a) b = 0) → S.hT F.fl.z b = T →
      F.fl.z + b ∈ orth S (Xplus F) := by
    intro b hbe hbz
    rw [Xplus, mem_orth_Xplus]
    refine ⟨fun a => ?_, ?_⟩
    · rw [map_add, F.fl.z_orth a, hbe a, add_zero]
    · rw [map_add, F.fl.z_norm, hbz, neg_add_cancel]

  have hconcl : ∀ (F₂ : LFlag S r T'), F₂.zt = F₂.fl.z → ∀ b x x₂ : S.V, (∀ a, S.hT (F.fl.e a) b = 0) →
      S.hT F.fl.z b = T → x ∈ Xsp F → x₂ ∈ Xsp F₂ →
      F.fl.z + b - 0 = ((1 : E) • F.zt + x) + ((0 : E) • F₂.zt + x₂) → Dl F.fl F₂.fl r = 0 := by
    intro F₂ _ b x x₂ hbe hbz hx hx₂ heq
    rw [hz, one_smul, zero_smul, zero_add, sub_zero] at heq
    have hx₂e : x₂ = b - x := by
      calc x₂ = (F.fl.z + x + x₂) - F.fl.z - x := by abel
        _ = (F.fl.z + b) - F.fl.z - x := by rw [heq]
        _ = b - x := by abel
    have hx₂z : S.hT F.fl.z x₂ = T := by rw [hx₂e, map_sub, hbz, hzX x hx, sub_zero]
    refine Dr_zero_of F.fl F₂.fl hx₂ ?_ fun a => ?_
    · rintro rfl
      rw [map_zero] at hx₂z
      exact hT hx₂z.symm
    · rw [hx₂e, map_sub, hbe a, heX x hx a, sub_zero]
  constructor
  ·
    intro hD
    obtain ⟨b, hbX, hbe, hbz⟩ := exists_b F.fl F'.fl hG' hD
    have hyU1 : F.fl.z + b ∈ UUE Λ F F' := by
      rw [hU1]
      refine Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), by simp [fvec_last]⟩) ?_
      have hXs : F'.fl.X ≤ Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)) := by
        rw [FlagG.X, Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        exact Submodule.subset_span ⟨Sum.inr (Fin.castSucc a), by simp [fvec_castSucc]⟩
      exact hXs hbX
    have hyU2 : F.fl.z + b ∈ UUE Λ F F'' := by
      rw [← orth_orth S (UUE Λ F F''), mem_orth]
      intro v hv
      have hv' : v ∈ Th'' Λ F F' F'' β := by rw [hTh''eq]; exact hv
      obtain ⟨p, hp, rfl⟩ := hv'
      have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
      have e1 : S.hT p.1 (F.fl.z + b) = 0 := by
        have := (mem_orth S).1 hm.1 _ hyU1
        rw [hT_swap, this, star_zero]
      have e2 : S.hT (p.1 - p.2) (F.fl.z + b) = 0 :=
        (mem_orth S).1 (hyo b hbe hbz) _ (Submodule.mem_sup_left hm.2.2.1)
      have : p.2 = p.1 - (p.1 - p.2) := by abel
      show S.hT p.2 (F.fl.z + b) = 0
      rw [this, hT_sub_left, e1, e2, sub_zero]
    have hsg : SgRel F F' (F.fl.z + b) 0 1 0 :=
      ⟨0, Submodule.zero_mem _, b, hbX, by rw [hz]; simp⟩
    obtain ⟨x, hx, x₂, hx₂, heq⟩ := (key _ ⟨hyU1, hyo b hbe hbz⟩ ⟨hyU2, hyo b hbe hbz⟩).1 hsg
    exact hconcl F'' hz'' b x x₂ hbe hbz hx hx₂ heq
  ·
    intro hD
    obtain ⟨b, hbX, hbe, hbz⟩ := exists_b F.fl F''.fl hG'' hD
    have hyU2 : F.fl.z + b ∈ UUE Λ F F'' := by
      rw [hU2]
      refine Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), by simp [fvec_last]⟩) ?_
      have hXs : F''.fl.X ≤ Submodule.span E (Set.range (Sum.elim F.fl.fvec F''.fl.fvec)) := by
        rw [FlagG.X, Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        exact Submodule.subset_span ⟨Sum.inr (Fin.castSucc a), by simp [fvec_castSucc]⟩
      exact hXs hbX
    have hyU1 : F.fl.z + b ∈ UUE Λ F F' := by
      rw [← orth_orth S (UUE Λ F F'), mem_orth]
      intro v hv
      have hv' : v ∈ Th Λ F F' F'' β := by rw [hTheq]; exact hv
      obtain ⟨p, hp, rfl⟩ := hv'
      have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
      have e1 : S.hT p.2 (F.fl.z + b) = 0 := by
        have := (mem_orth S).1 hm.2.1 _ hyU2
        rw [hT_swap, this, star_zero]
      have e2 : S.hT (p.1 - p.2) (F.fl.z + b) = 0 :=
        (mem_orth S).1 (hyo b hbe hbz) _ (Submodule.mem_sup_left hm.2.2.1)
      have : p.1 = (p.1 - p.2) + p.2 := by abel
      show S.hT p.1 (F.fl.z + b) = 0
      rw [this, hT_add_left, e1, e2, add_zero]
    have hsg : SgRel F F'' (F.fl.z + b) 0 1 0 :=
      ⟨0, Submodule.zero_mem _, b, hbX, by rw [hz]; simp⟩
    obtain ⟨x, hx, x₂, hx₂, heq⟩ := (key _ ⟨hyU1, hyo b hbe hbz⟩ ⟨hyU2, hyo b hbe hbz⟩).2 hsg
    exact hconcl F' hz' b x x₂ hbe hbz hx hx₂ heq

end Core

end PI.ScalarPairDr.W
end
end

section
noncomputable section

open scoped Classical

namespace PI.ScalarPairDr.W

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ddS_ne_zero (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

theorem exists_ne_zero_mem (D : D7) (j : ℤ) :
    ∃ x : D.host.E, x ≠ 0 ∧ x ∈ (ddS D ^ j : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have h : ddS D ^ j ≠ 0 := zpow_ne_zero j (ddS_ne_zero D)
  by_contra hne
  push_neg at hne
  apply h
  rw [FractionalIdeal.eq_zero_iff]
  intro x hx
  by_contra hx0
  exact hne x hx0 hx

theorem X_le_spanE_XS (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) :
    F0.X ≤ spanE (VS D) (XS D F0) := by
  unfold FlagG.X spanE
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem D (-((D.R.rS : ℤ) - (a : ℕ)))
  have hmem : x • F0.e a ∈ (XS D F0 : Set (VS D).V) := by
    unfold XS
    exact Submodule.subset_span ⟨a, x, hx, rfl⟩
  have h2 : x • F0.e a ∈ Submodule.span D.host.E (XS D F0 : Set (VS D).V) := Submodule.subset_span hmem
  have h3 := Submodule.smul_mem _ x⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ hx0, one_smul] at h3

theorem Tu_ne_zero (D : D7) (u : D.what₂.Word) : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by
  unfold Tu
  exact_mod_cast (D.mem u).A.T_prime.ne_zero

theorem scalarDr (D : D7) (u u' : D.what₂.Word) : PI.ScalarPairDr.ScalarDr D u u' := by
  intro F0 what₂ hrows Λ hΛ x y hGx hGy β _hpair hs hsc
  have hrow := hrows.1 Λ hΛ
  have hXF : Xsp (lf D F0) ≤ spanE (VS D) (XLam Λ (lf D F0)) := by
    rw [hrow.2.2]
    exact X_le_spanE_XS D F0
  have hXx : Xsp x.1 ≤ spanE (VS D) (XLam Λ x.1) := by
    rw [x.2.2.2.2]
    exact X_le_spanE_XS D x.1.fl
  have hXy : Xsp y.1 ≤ spanE (VS D) (XLam Λ y.1) := by
    rw [y.2.2.2.2]
    exact X_le_spanE_XS D y.1.fl
  exact core Λ D.R.k (lf D F0) x.1 y.1 β rfl x.2.1.2 y.2.1.2 hXF hXx hXy
    (PI.UnitaryGroupMassFormula.BetaLUniq.finrank_hS D) (Tu_ne_zero D u) hGx hGy hs hsc

end D7

end PI.ScalarPairDr.W
end
end
