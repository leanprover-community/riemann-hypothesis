import Formalism.PeriodIntegrals.FglGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.ExpCongruenceExtendsToSum

section
noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhDualGram

open PI.FglGram MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

section Rename₂

variable {σ τ : Type} [Finite σ] (r : σ → τ)

theorem hasSubst_ren : HasSubst (fun s => (X (r s) : MvPowerSeries τ ℂ_[p])) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_X _)

def ren : MvPowerSeries σ ℂ_[p] →ₐ[ℂ_[p]] MvPowerSeries τ ℂ_[p] :=
  substAlgHom (hasSubst_ren r)

theorem ren_apply (F : MvPowerSeries σ ℂ_[p]) :
    ren r F = MvPowerSeries.subst (fun s => (X (r s) : MvPowerSeries τ ℂ_[p])) F :=
  substAlgHom_apply _ F

theorem ren_psubst (P : PowerSeries ℂ_[p]) {y : MvPowerSeries σ ℂ_[p]} (hy : constantCoeff y = 0) :
    ren r (PowerSeries.subst y P) = PowerSeries.subst (ren r y) P := by
  rw [ren_apply, ren_apply, PowerSeries.subst, PowerSeries.subst]
  exact MvPowerSeries.subst_comp_subst_apply
    (PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.of_constantCoeff_zero hy)) (hasSubst_ren r) P

theorem ren_X (s : σ) : ren r (X s : MvPowerSeries σ ℂ_[p]) = X (r s) := by
  rw [ren_apply, MvPowerSeries.subst_X (hasSubst_ren r)]

theorem ren_C (c : ℂ_[p]) : ren r (C c : MvPowerSeries σ ℂ_[p]) = C c := by
  rw [ren_apply, MvPowerSeries.subst_C]

theorem simeq_ren {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq (ren r f) (ren r g) := by
  obtain ⟨h0, h1⟩ := h
  have hs : ren r f - ren r g = ren r (f - g) := (map_sub _ _ _).symm
  have hc : constantCoeff (ren r (f - g)) = 0 := by
    rw [ren_apply]
    exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_ren r) (fun _ => constantCoeff_X _) h0
  refine ⟨by rw [hs, hc], fun n => ?_⟩
  have e1 : expMv (ren r (f - g)) = PI.FglPhSplit.expMv (ren r (f - g)) := rfl
  have e0 : expMv (f - g) = PI.FglPhSplit.expMv (f - g) := rfl
  have h1' : PI.FglPhSplit.Wk.AllIn (Wp p) (PI.FglPhSplit.expMv (f - g)) := fun n => by
    rw [← e0]; exact h1 n
  rw [hs, e1, PI.FglPhSplit.Wk.expMv_eq_subst hc, ← ren_psubst r _ h0,
    ← PI.FglPhSplit.Wk.expMv_eq_subst h0, ren_apply]
  exact PI.FglPhSplit.Wk.allIn_subst_X r (hasSubst_ren r) h1' n

variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hl0 : PowerSeries.constantCoeff l = 0)

omit [Finite σ] in
include hl0 in
theorem cc_lin {ι' : Type} [Fintype ι'] (c : ι' → ℂ_[p]) (w : ι' → MvPowerSeries σ ℂ_[p])
    (hw : ∀ j, constantCoeff (w j) = 0) :
    constantCoeff (∑ j, C (c j) * lg l (w j)) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => by
    rw [map_mul, lg, PI.FglPhSplit.Wk.cc_psubst _ hl0 (hw j), mul_zero]

include hl0 in
theorem ren_lin {ι' : Type} [Fintype ι'] (c : ι' → ℂ_[p]) (w : ι' → MvPowerSeries σ ℂ_[p])
    (hw : ∀ j, constantCoeff (w j) = 0) :
    ren r (lin l ex c w) = lin l ex c (fun j => ren r (w j)) := by
  unfold lin pt
  rw [ren_psubst r _ (cc_lin hl0 c w hw), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ren_C, lg, lg, ren_psubst r _ (hw j)]

omit [Finite σ] in
include hex0 hl0 in
theorem ren_PhOn {κ T : Type} [Fintype κ] [Fintype T] {n : ℕ} (E : T ≃ Fin n)
    (B : T → κ → ℂ_[p] × ℂ_[p]) :
    ren (p := p) E.symm (PhOn l ex ph (fun j => B (E.symm j))) = PhOn l ex ph B := by
  unfold PhOn phAt
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hw : ∀ j : Fin n, constantCoeff (Xv j : MvPowerSeries (Fin n) ℂ_[p]) = 0 :=
    fun j => constantCoeff_X j
  have h0 : constantCoeff (lin l ex (fun j => (B (E.symm j) k).1)
      (fun j => (Xv j : MvPowerSeries (Fin n) ℂ_[p]))) = 0 := by
    unfold lin pt
    exact PI.FglPhSplit.Wk.cc_psubst _ hex0 (cc_lin hl0 _ _ hw)
  rw [ren_psubst _ _ h0, ren_lin _ hl0 _ _ hw]
  simp only [Xv, ren_X]
  congr 1
  unfold lin
  congr 1
  exact Equiv.sum_comp E.symm (fun e => C (B e k).1 * lg l (X e : MvPowerSeries T ℂ_[p]))

end Rename₂

end PI.UnitaryGroupMassFormula.PhDualGram

end
end

section
noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhDualGram

open PI.FglGram MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}

theorem cc_add (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {σ : Type} {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    constantCoeff (add l ex x y) = 0 := by
  unfold add pt lg
  exact PI.FglPhSplit.Wk.cc_psubst _ hex0 (by
    rw [map_add, PI.FglPhSplit.Wk.cc_psubst _ hl0 hx, PI.FglPhSplit.Wk.cc_psubst _ hl0 hy, add_zero])

theorem ren_be (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {σ τ : Type} [Finite σ] (r : σ → τ) {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    ren r (be l ex ph x y) = be l ex ph (ren r x) (ren r y) := by
  unfold be phAt
  rw [map_sub, map_sub, ren_psubst r _ (cc_add hex0 hl0 hx hy), ren_psubst r _ hx, ren_psubst r _ hy]
  congr 3
  unfold add pt lg
  rw [ren_psubst r _ (by rw [map_add, PI.FglPhSplit.Wk.cc_psubst _ hl0 hx,
    PI.FglPhSplit.Wk.cc_psubst _ hl0 hy, add_zero]), map_add, ren_psubst r _ hx, ren_psubst r _ hy]

theorem mulBy_one (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {σ : Type} {x : MvPowerSeries σ ℂ_[p]}
    (hx : constantCoeff x = 0) : mulBy l ex 1 x = x := by
  unfold mulBy
  rw [map_one, one_mul]
  exact PI.FglPhSplit.Wk.pt_lg (⟨l, ex, 0⟩ : PI.FglPhSplit.Dat ℂ_[p]) hl0 hinvl hx

theorem be_mulBy_zero (hex0 : PowerSeries.constantCoeff ex = 0)
    (hph0 : PowerSeries.constantCoeff ph = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {σ : Type} (x : MvPowerSeries σ ℂ_[p])
    {y : MvPowerSeries σ ℂ_[p]} (hy : constantCoeff y = 0) :
    be l ex ph (mulBy l ex 0 x) y = 0 :=
  PI.FglPhSplit.Wk.be_mulBy_zero (⟨l, ex, ph⟩ : PI.FglPhSplit.Dat ℂ_[p]) hex0 hph0 hl0 hinvl x hy

theorem gramRhs_dual (hex0 : PowerSeries.constantCoeff ex = 0)
    (hph0 : PowerSeries.constantCoeff ph = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {κ ι : Type} [Fintype κ] [Fintype ι]
    (b b' : ι → κ → ℂ_[p] × ℂ_[p]) (hI : DualIso b b') {n : ℕ} (E : ι ⊕ ι ≃ Fin n)
    (hE : ∀ e e', E (Sum.inl e) < E (Sum.inr e')) :
    GramRhs l ex ph (fun j => Sum.elim b b' (E.symm j)) =
      ∑ e, be l ex ph (Xv (E (Sum.inl e))) (Xv (E (Sum.inr e))) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hdiag : ∀ x : ι ⊕ ι, hP (Sum.elim b b' x) (Sum.elim b b' x) = 0 := by
    rintro (e | e)
    exacts [h1 e e, h2 e e]
  have hXv : ∀ j : Fin n, constantCoeff (Xv j : MvPowerSeries (Fin n) ℂ_[p]) = 0 :=
    fun j => constantCoeff_X j
  have bz : ∀ (x : MvPowerSeries (Fin n) ℂ_[p]) (j : Fin n), be l ex ph (mulBy l ex 0 x) (Xv j) = 0 :=
    fun x j => be_mulBy_zero hex0 hph0 hl0 hinvl x (hXv j)
  have hE' : ∀ e e', ¬ E (Sum.inr e) < E (Sum.inl e') := fun e e' h => lt_asymm h (hE e' e)
  have hmix : ∀ e e', be l ex ph (mulBy l ex (hP (b e) (b' e')).1 (Xv (E (Sum.inl e))))
      (Xv (E (Sum.inr e'))) = if e = e' then be l ex ph (Xv (E (Sum.inl e))) (Xv (E (Sum.inr e'))) else 0 := by
    intro e e'
    rw [h3]
    split_ifs
    · rw [Prod.fst_one, mulBy_one hl0 hinvl (hXv _)]
    · rw [Prod.fst_zero, bz]
  unfold GramRhs
  rw [Finset.sum_eq_zero (fun j _ => by rw [hdiag, Prod.fst_zero, map_zero, zero_mul]), zero_add]
  simp only [Finset.sum_filter]
  rw [← E.sum_comp]
  refine (Finset.sum_congr rfl fun x _ => by rw [← E.sum_comp]).trans ?_
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, h1, h2,
    Prod.fst_zero, bz, ite_self, Finset.sum_const_zero, hE, hE', if_true, if_false, hmix, zero_add,
    add_zero, Finset.sum_ite_eq]
  simp

end PI.UnitaryGroupMassFormula.PhDualGram

end
end
