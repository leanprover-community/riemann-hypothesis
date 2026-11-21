import Formalism.GaussJetBounds.StatementN
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

section Analytic

variable {K : Type u} [Field K] {ι : Type} [Fintype ι]

def dirD (L : ι → K) : Derivation K (MvPowerSeries ι K) (MvPowerSeries ι K) :=
  ∑ x, L x • MvPowerSeries.pderiv K x

lemma dirD_apply (L : ι → K) (F : MvPowerSeries ι K) :
    dirD L F = ∑ x, MvPowerSeries.C (L x) * MvPowerSeries.pderiv K x F := by
  unfold dirD
  have h := congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := K) (A := MvPowerSeries ι K)
    (M := MvPowerSeries ι K)) (fun x => L x • MvPowerSeries.pderiv K x) Finset.univ) F
  rw [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, MvPowerSeries.smul_eq_C_mul]



lemma dirD_X (L : ι → K) (x : ι) : dirD L (MvPowerSeries.X x) = MvPowerSeries.C (L x) := by
  classical
  rw [dirD_apply, Finset.sum_eq_single x]
  · rw [MvPowerSeries.pderiv_X_self, mul_one]
  · intro y _ hy
    rw [MvPowerSeries.pderiv_X_of_ne hy.symm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ x) h

lemma dirD_C (L : ι → K) (a : K) : dirD L (MvPowerSeries.C a : MvPowerSeries ι K) = 0 := by
  rw [dirD_apply]
  simp

def linSer (c : ι → ι → K) (L : ι → K) : MvPowerSeries ι K :=
  ∑ x, ∑ y, MvPowerSeries.C (c x y) *
    (MvPowerSeries.C (L x) * MvPowerSeries.X y + MvPowerSeries.C (L y) * MvPowerSeries.X x)





lemma polar_comm (c : ι → ι → K) (L L' : ι → K) : polar c L L' = polar c L' L := by
  unfold polar
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring


end Analytic

section Exp

variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]


lemma constantCoeff_mvExp (f : MvPowerSeries ι K) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (mvExp f) = 1 := by
  unfold mvExp
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [hf, hn]


end Exp

section Comb

variable {n : ℕ}

def invOn (s : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ * σ = 1 ∧ ∀ i, i ∉ s → σ i = i)

lemma mem_invOn {s : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} :
    σ ∈ invOn s ↔ σ * σ = 1 ∧ ∀ i, i ∉ s → σ i = i := by
  simp [invOn]


lemma swap_mul_apply_left {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτa : τ a = a) :
    (Equiv.swap a b * τ) a = b := by
  rw [Equiv.Perm.mul_apply, hτa, Equiv.swap_apply_left]

lemma swap_mul_apply_right {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτb : τ b = b) :
    (Equiv.swap a b * τ) b = a := by
  rw [Equiv.Perm.mul_apply, hτb, Equiv.swap_apply_right]

variable {R : Type u} [CommRing R]

def edgeW (w : Fin n → Fin n → R) (σ : Equiv.Perm (Fin n)) : R :=
  ∏ i ∈ Finset.univ.filter (fun i => i < σ i), w i (σ i)







end Comb

section Main

variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]


end Main


end Formalism.DworkPowerSeriesWeights
