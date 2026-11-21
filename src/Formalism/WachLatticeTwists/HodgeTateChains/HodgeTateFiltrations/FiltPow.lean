import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic


theorem filtPow : StatFiltPow := by
  intro ℓ hℓ N _ F γ hF0 hanti hstep b hb x

  set M := ℓ ^ (b - 1) with hM
  let P : AddSubgroup N := (nsmulAddMonoidHom (α := N) (ℓ ^ 2)).range ⊔ F M
  have hP : ∀ v ∈ P, ∃ y : N, ∃ z ∈ F M, v = (ℓ ^ 2) • y + z := by
    intro v hv
    obtain ⟨p, ⟨y, rfl⟩, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    exact ⟨y, z, hz, rfl⟩
  apply hP
  let G : Module.End ℤ N := γ.toIntLinearMap
  let Y : Module.End ℤ N := G - 1
  have hY : ∀ v, Y v = γ v - v := fun v => by simp [Y, G]
  have hYk : ∀ k, (Y ^ k) x ∈ F k := by
    intro k
    induction k with
    | zero => rw [hF0]; trivial
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, hY]
      exact hstep k _ ih
  have hmono : ∀ k, M ≤ k → F k ≤ F M := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_refl _
    | succ k _ ih => exact le_trans (hanti k) ih
  have hγ : G = Y + 1 := by simp [Y]
  have hpow : (⇑γ)^[ℓ ^ b] x = ((Y + 1) ^ (ℓ ^ b)) x := by
    rw [← hγ, Module.End.pow_apply]; rfl
  rw [hpow, (Commute.one_right Y).add_pow, Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
  rw [LinearMap.add_apply, Module.End.one_apply, add_sub_cancel_right, LinearMap.sum_apply]
  apply AddSubgroup.sum_mem
  intro k _
  have hterm : (Y ^ (k + 1) * ((ℓ ^ b).choose (k + 1) : Module.End ℤ N)) x
      = ((ℓ ^ b).choose (k + 1)) • (Y ^ (k + 1)) x := by
    rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
  rw [hterm]
  by_cases hk : k + 1 < M
  · obtain ⟨t, ht⟩ := binom ℓ hℓ b (k + 1) hb (Nat.succ_pos k) hk
    apply AddSubgroup.mem_sup_left
    refine ⟨t • (Y ^ (k + 1)) x, ?_⟩
    rw [ht, mul_smul]; rfl
  · apply AddSubgroup.mem_sup_right
    exact (F M).nsmul_mem (hmono _ (by omega) (hYk _)) _

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
