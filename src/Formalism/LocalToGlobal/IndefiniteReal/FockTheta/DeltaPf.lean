import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.SquareNormIntegralNonneg
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HookBound

noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace Formalism.IndefR.Fock.DeltaPf

open Formalism.REAL

theorem fockF_eq_sum_of_subset {σ : Type*} {f g : MvPolynomial σ ℂ} {s : Finset (σ →₀ ℕ)} (h : f.support ⊆ s) :
    fockF f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  refine Finset.sum_subset h ?_
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fockF_one {σ : Type*} : fockF (1 : MvPolynomial σ ℂ) 1 = 1 := by
  classical
  rw [fockF_eq_sum_of_subset (s := {0})]
  · simp
  · intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    rw [Finset.mem_singleton]
    by_contra h0
    exact hm (if_neg (Ne.symm h0))


theorem fockF_rename {σ τ : Type*} {i : σ → τ} (hi : Function.Injective i) (f g : MvPolynomial σ ℂ) :
    fockF (rename i f) (rename i g) = fockF f g := by
  classical
  unfold fockF
  rw [MvPolynomial.support_rename_of_injective hi, Finset.sum_image (by
    intro a _ b _ hab
    exact Finsupp.mapDomain_injective hi hab)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain i hi, MvPolynomial.coeff_rename_mapDomain i hi,
    Finsupp.mapDomain_support_of_injective hi, Finset.prod_image (by
      intro a _ b _ hab
      exact hi hab)]
  simp only [Finsupp.mapDomain_apply hi]





theorem rename_mem_supported {σ τ : Type*} (i : σ → τ) (f : MvPolynomial σ ℂ) :
    rename i f ∈ supported ℂ (Set.range i) := by
  classical
  rw [MvPolynomial.mem_supported]
  intro v hv
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename i f (Finset.mem_coe.1 hv))
  exact ⟨w, rfl⟩

def PmEq {R : Type*} [Ring R] (f g : R) : Prop := f = g ∨ f = -g

theorem PmEq.mul {R : Type*} [Ring R] {f g f' g' : R} (h : PmEq f g) (h' : PmEq f' g') : PmEq (f * f') (g * g') := by
  unfold PmEq at *
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (mul_neg _ _)
  · exact Or.inr (neg_mul _ _)
  · exact Or.inl (neg_mul_neg _ _)

theorem PmEq.pow {R : Type*} [Ring R] {f g : R} (h : PmEq f g) (k : ℕ) : PmEq (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact Or.inl (by rw [pow_zero, pow_zero])
  | succ k ih => simpa only [pow_succ] using ih.mul h

theorem PmEq.prod {ι R : Type*} [CommRing R] (s : Finset ι) (f g : ι → R) (h : ∀ i ∈ s, PmEq (f i) (g i)) :
    PmEq (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))



theorem PmEq.mem {σ : Type*} {S : Set σ} {f g : MvPolynomial σ ℂ} (h : PmEq f g) (hg : g ∈ supported ℂ S) :
    f ∈ supported ℂ S := by
  unfold PmEq at h
  rcases h with rfl | rfl
  · exact hg
  · exact neg_mem hg


section Spec

variable {D : D7} {m n : ℕ}

def iotaP (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) (v : Fin P × Fin P) : FVar D m n :=
  (τ, Fin.castLE hm v.2, Fin.castLE hn v.1)

def embedding₂ (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n) (v : Fin Q × Fin Q) : FVar D m n :=
  (τ, ⟨P + v.2, by have := v.2.isLt; omega⟩, ⟨n - 1 - v.1, by have := v.1.isLt; omega⟩)



def psiP (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) :
    MvPolynomial (Fin P × Fin P) ℚ →+* MvPolynomial (FVar D m n) ℂ :=
  (rename (iotaP τ hm hn)).toRingHom.comp (map (algebraMap ℚ ℂ))

def psiM (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n) :
    MvPolynomial (Fin Q × Fin Q) ℚ →+* MvPolynomial (FVar D m n) ℂ :=
  (rename (embedding₂ τ P hm hn)).toRingHom.comp (map (algebraMap ℚ ℂ))

theorem minorPlus_eq (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) (k : ℕ) (hk : k ≤ P) (hk' : k ≤ P) :
    psiP τ hm hn (Formalism.GradedWeylDivisibility.lpMinor ℚ k hk hk') = minorPlus τ k := by
  unfold minorPlus Formalism.GradedWeylDivisibility.lpMinor
  rw [RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun α β => ?_)
  have hα := α.isLt
  have hβ := β.isLt
  simp [psiP, iotaP, varF, RingHom.mapMatrix_apply]
  split_ifs with h
  · rfl
  · exact absurd ⟨by omega, by omega⟩ h

theorem minorMinus_eq (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n) (k : ℕ) (hk : k ≤ Q)
    (hk' : k ≤ Q) :
    minorMinus τ P k =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) : MvPolynomial (FVar D m n) ℂ) *
        psiM τ P hm hn (Formalism.GradedWeylDivisibility.lpMinor ℚ k hk hk') := by
  unfold minorMinus Formalism.GradedWeylDivisibility.lpMinor
  rw [RingHom.map_det, ← Matrix.det_permute]
  refine congrArg Matrix.det (Matrix.ext fun α β => ?_)
  have hα := α.isLt
  have hβ := β.isLt
  simp [psiM, embedding₂, varF, RingHom.mapMatrix_apply, Fin.revPerm_apply]
  split_ifs with h
  · first
      | rfl
      | (congr 1
         refine Prod.ext rfl (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;> (try simp [Fin.val_rev]) <;> omega)
      | (simp [Fin.val_rev]; omega)
  · exact absurd ⟨by omega, by omega⟩ h



end Spec

section Asm

variable {D : D7} {m n : ℕ}




theorem psiM_mem (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n)
    (x : MvPolynomial (Fin Q × Fin Q) ℚ) :
    psiM τ P hm hn x ∈ supported ℂ {v : FVar D m n | v.1 = τ ∧ P ≤ (v.2.1 : ℕ)} := by
  show rename (embedding₂ τ P hm hn) (map (algebraMap ℚ ℂ) x) ∈ _
  refine MvPolynomial.supported_mono ?_ (rename_mem_supported (embedding₂ τ P hm hn) _)
  rintro _ ⟨v, rfl⟩
  simp [embedding₂]



end Asm


end Formalism.IndefR.Fock.DeltaPf

end
