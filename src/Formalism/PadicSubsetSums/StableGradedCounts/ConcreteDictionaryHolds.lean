import Formalism.PadicSubsetSums.CentralIdempotents.GL2UnipotentBruhatDecomposition

namespace Formalism.IrreducibleCountingLemmas.WindowSums

namespace ConcreteDictionaryLemmas
open PowerSeries

section ode
variable {R : Type*} [CommRing R] [IsAddTorsionFree R]

theorem ode_coeff (c : R) (f : R⟦X⟧) (hf : (1 + X) * d⁄dX R f = C c * f) (n : ℕ) :
    ((n : R) + 1) * coeff (n + 1) f = (c - n) * coeff n f := by
  have h := congrArg (coeff n) hf
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul] at h
  cases n with
  | zero =>
    simp only [coeff_zero_X_mul, add_zero] at h
    simp only [Nat.cast_zero, zero_add, sub_zero, one_mul] at h ⊢
    simpa using h
  | succ m =>
    rw [coeff_succ_X_mul, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination h

theorem ode_unique (c : R) (f g : R⟦X⟧) (hf : (1 + X) * d⁄dX R f = C c * f)
    (hg : (1 + X) * d⁄dX R g = C c * g) (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have h1 := ode_coeff c f hf n
    have h2 := ode_coeff c g hg n
    rw [ih, ← h2] at h1
    have h3 : (n + 1) • coeff (n + 1) f = (n + 1) • coeff (n + 1) g := by
      simpa [nsmul_eq_mul] using h1
    exact nsmul_right_injective (Nat.succ_ne_zero n) h3

end ode

variable {l : ℕ} [Fact l.Prime]

theorem bin_ode (c : ℤ_[l]) :
    (1 + X) * d⁄dX ℤ_[l] (binomialSeries ℤ_[l] c) = C c * binomialSeries ℤ_[l] c := by
  ext n
  have key : ∀ n : ℕ, ((n : ℤ_[l]) + 1) * Ring.choose c (n + 1) = Ring.choose c n * (c - n) := by
    intro n
    have := Ring.choose_smul_choose c (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one, Nat.choose_succ_self_right, add_tsub_cancel_left,
      Ring.choose_one_right, nsmul_eq_mul] at this
    push_cast at this
    exact this
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul]
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
  cases n with
  | zero =>
    have := key 0
    simp only [coeff_zero_X_mul, add_zero]
    simp only [Nat.cast_zero, zero_add, sub_zero, one_mul] at this ⊢
    rw [mul_one, this, mul_comm]
  | succ m =>
    rw [coeff_succ_X_mul, coeff_derivative]
    simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
    have := key (m + 1)
    push_cast at this ⊢
    linear_combination this

theorem brk_const (a : ℤ_[l]) : constantCoeff (brk l a) = 0 := by
  simp [brk]

theorem brk_hasSubst (a : ℤ_[l]) : HasSubst (brk l a) :=
  HasSubst.of_constantCoeff_zero' (brk_const a)

theorem const_subst (h f : PowerSeries ℤ_[l]) (hh : constantCoeff h = 0) :
    constantCoeff (subst h f) = constantCoeff f := by
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh
  have h1 : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add]
  have h2 : constantCoeff (subst h (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero hh _ (by simp)
  rw [h2, add_zero, subst_C]
  exact constantCoeff_C _

theorem bin_comp (a b : ℤ_[l]) :
    subst (brk l b) (binomialSeries ℤ_[l] a) = binomialSeries ℤ_[l] (a * b) := by
  have hs := brk_hasSubst b
  apply ode_unique (a * b) _ _ _ (bin_ode _)
  · rw [const_subst _ _ (brk_const b)]; simp
  · rw [derivative_subst hs]
    have h1 : d⁄dX ℤ_[l] (brk l b) = d⁄dX ℤ_[l] (binomialSeries ℤ_[l] b) := by
      simp [brk]
    have h2 : (1 + X : PowerSeries ℤ_[l]).subst (brk l b) = binomialSeries ℤ_[l] b := by
      rw [subst_add hs, subst_X hs, ← map_one C, subst_C]
      simp [brk]
    have h3 := congrArg (subst (brk l b)) (bin_ode a)
    rw [subst_mul hs, subst_mul hs, h2, subst_C] at h3
    have h4 := bin_ode b
    rw [h1]
    calc (1 + X) * (subst (brk l b) (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] a)) *
            d⁄dX ℤ_[l] (binomialSeries ℤ_[l] b))
        = subst (brk l b) (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] a)) *
            ((1 + X) * d⁄dX ℤ_[l] (binomialSeries ℤ_[l] b)) := by ring
      _ = C b * (binomialSeries ℤ_[l] b *
            subst (brk l b) (d⁄dX ℤ_[l] (binomialSeries ℤ_[l] a))) := by rw [h4]; ring
      _ = _ := by
        rw [h3, map_mul]
        have : (MvPowerSeries.C a : MvPowerSeries Unit ℤ_[l]) = (C a : PowerSeries ℤ_[l]) := rfl
        rw [this]; ring

theorem brk_comp (a b : ℤ_[l]) : subst (brk l b) (brk l a) = brk l (a * b) := by
  have hs := brk_hasSubst b
  change subst (brk l b) (binomialSeries ℤ_[l] a - 1) = _
  rw [subst_sub hs, bin_comp, ← map_one C, subst_C]
  simp [brk]

theorem brk_factor (a : ℤ_[l]) :
    ∃ g : PowerSeries ℤ_[l], brk l a = X * g ∧ constantCoeff g = a := by
  refine ⟨PowerSeries.mk fun n => coeff (n + 1) (brk l a), ?_, ?_⟩
  · ext n
    cases n with
    | zero => simp [brk_const]
    | succ m => rw [coeff_succ_X_mul, coeff_mk]
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp [brk, binomialSeries_coeff, coeff_one]

theorem exists_prim (e s : ℕ) (h : e * s = l - 1) : ∃ ω : ℤ_[l], IsPrimitiveRoot ω s := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ZMod l) (l - 1)
  have inj : Function.Injective (WittVector.teichmuller l : ZMod l →* WittVector l (ZMod l)) := by
    intro x y hxy
    have := congrArg (fun w => WittVector.coeff w 0) hxy
    simpa [WittVector.teichmuller_coeff_zero] using this
  have h1 := hζ.map_of_injective inj
  have h2 := h1.map_of_injective (f := WittVector.equiv l) (WittVector.equiv l).injective
  exact ⟨_, h2.pow (by omega) h.symm⟩


theorem subst_prod {ι : Type*} (h : PowerSeries ℤ_[l]) (hs : HasSubst h) (t : Finset ι)
    (f : ι → PowerSeries ℤ_[l]) : subst h (∏ i ∈ t, f i) = ∏ i ∈ t, subst h (f i) := by
  rw [← coe_substAlgHom hs, map_prod]

end ConcreteDictionaryLemmas

open PowerSeries ConcreteDictionaryLemmas


end Formalism.IrreducibleCountingLemmas.WindowSums
