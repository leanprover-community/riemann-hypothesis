import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZGlueA

noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsKCRT

open NumberField Matrix IsDedekindDomain Formalism.MainNotions.S Formalism.L2.SG.Pf.unitaryCongruence
open scoped TensorProduct

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def pm (u : R) (X : Matrix n n R) : Matrix n n R := 1 + u • (X - 1)

theorem pm_one (u : R) : pm u (1 : Matrix n n R) = 1 := by simp [pm]


theorem one_add_mul_one_add (a b : Matrix n n R) : (1 + a) * (1 + b) = 1 + a + b + a * b := by noncomm_ring

theorem pm_mul {u : R} (hu : u * u = u) (X Y : Matrix n n R) : pm u X * pm u Y = pm u (X * Y) := by
  have e : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  unfold pm
  rw [one_add_mul_one_add, smul_mul_smul_comm, hu, e, smul_add, smul_add]
  abel


theorem cT_pm (σ : R →+* R) {u : R} (hu : σ u = u) (X : Matrix n n R) :
    Formalism.UG.cT σ (pm u X) = pm u (Formalism.UG.cT σ X) := by
  ext a b
  simp only [Formalism.UG.cT, pm, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, map_add, map_mul, map_sub, hu, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · have h' : ¬ b = a := fun e => h e.symm
    simp [h, h']

theorem pm_form {u : R} (hu : u * u = u) (A J X : Matrix n n R) (h : A * J * X = J) :
    pm u A * J * pm u X = J := by
  have e : (A - 1) * J + J * (X - 1) + (A - 1) * J * (X - 1) = A * J * X - J := by noncomm_ring
  have e0 : (A - 1) * J + J * (X - 1) + (A - 1) * J * (X - 1) = 0 := by rw [e, h, sub_self]
  have key : (A - 1) * J * (X - 1) = -((A - 1) * J + J * (X - 1)) := eq_neg_of_add_eq_zero_right e0
  have e3 : ∀ a b : Matrix n n R, (1 + a) * J * (1 + b) = J + a * J + J * b + a * J * b := by
    intro a b; noncomm_ring
  unfold pm
  rw [e3, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, hu, key, smul_neg, smul_add]
  abel

end Alg

section Ad

variable {F : Type} [Field F] [NumberField F]

open LatDictZ.Z5

def Tm (m : ℕ) : Set (HeightOneSpectrum (𝓞 F)) := {v | ((m : ℕ) : 𝓞 F) ∈ v.asIdeal}

theorem natc (m : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (m : Af F) v = algebraMap (𝓞 F) (v.adicCompletion F) (m : 𝓞 F) := by
  rw [map_natCast]
  exact map_natCast (ev v) m

theorem comp_sub (a b : Af F) (v : HeightOneSpectrum (𝓞 F)) : (a - b) v = a v - b v := map_sub (ev v) a b

theorem eT_idem (T : Set (HeightOneSpectrum (𝓞 F))) : eT T * eT T = eT T := by
  refine FiniteAdeleRing.ext (K := F) fun v => ?_
  rw [comp_mul]
  by_cases hv : v ∈ T
  · rw [eT_of_mem hv, one_mul]
  · rw [eT_of_not hv, zero_mul]

theorem not_mem_of_coprime {m₁ m₂ : ℕ} (h : Nat.Coprime m₁ m₂) {v : HeightOneSpectrum (𝓞 F)}
    (h1 : v ∈ Tm (F := F) m₁) : ((m₂ : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro h2
  have hz := Nat.gcd_eq_gcd_ab m₁ m₂
  rw [h, Nat.cast_one] at hz
  have hO := congrArg (Int.cast : ℤ → 𝓞 F) hz
  push_cast at hO
  have h1' : ((m₁ : ℕ) : 𝓞 F) ∈ v.asIdeal := h1
  have : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [hO]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1') (Ideal.mul_mem_right _ _ h2)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

open Classical in
theorem compl_eq (m : ℕ) : ∃ c ∈ Formalism.UG.intAd F, 1 - eT (Tm (F := F) m) = (m : Af F) * c := by
  refine ⟨mkI (fun v => if v ∈ Tm (F := F) m then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) (m : 𝓞 F))⁻¹)
    (fun v => by split_ifs with h; exacts [zero_mem _, inv_mem' h]), mkI_mem _ _, ?_⟩
  refine FiniteAdeleRing.ext (K := F) fun v => ?_
  rw [comp_sub, LatDictZ.Z5.comp_one, comp_mul, natc, mkI_apply]
  by_cases hv : v ∈ Tm (F := F) m
  · rw [eT_of_mem hv, if_pos hv, sub_self, mul_zero]
  · rw [eT_of_not hv, if_neg hv, sub_zero, mul_inv_cancel₀ (ne0 hv)]

open Classical in
theorem idem_eq {m₁ m₂ : ℕ} (h : Nat.Coprime m₁ m₂) :
    ∃ c ∈ Formalism.UG.intAd F, eT (Tm (F := F) m₁) = (m₂ : Af F) * c := by
  refine ⟨mkI (fun v => if v ∈ Tm (F := F) m₁ then (algebraMap (𝓞 F) (v.adicCompletion F) (m₂ : 𝓞 F))⁻¹ else 0)
    (fun v => by split_ifs with hv; exacts [inv_mem' (not_mem_of_coprime h hv), zero_mem _]), mkI_mem _ _, ?_⟩
  refine FiniteAdeleRing.ext (K := F) fun v => ?_
  rw [comp_mul, natc, mkI_apply]
  by_cases hv : v ∈ Tm (F := F) m₁
  · rw [eT_of_mem hv, if_pos hv, mul_inv_cancel₀ (ne0 (not_mem_of_coprime h hv))]
  · rw [eT_of_not hv, if_neg hv, mul_zero]

end Ad

section Inst

variable (I : AutInst)

open LatDictZ.Z5

theorem sig_iA (a : Af I.F) : Formalism.UG.sigR I.cm.sig (Af I.F) (iA I a) = iA I a := by
  simp [Formalism.UG.sigR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem fmat_mul_inv' (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  rw [← fmat_mul, mul_inv_cancel, fmat_one]

def mkG (u : I.E ⊗[I.F] Af I.F) (hu : u * u = u) (hσ : Formalism.UG.sigR I.cm.sig (Af I.F) u = u) (x : I.Gf) : I.Gf :=
  ⟨⟨pm u (I.fmat x), pm u (I.fmat x⁻¹),
    by rw [pm_mul hu, fmat_mul_inv', pm_one], by rw [pm_mul hu, fmat_inv_mul, pm_one]⟩, by
    have hx : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        I.fmat x = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (pm u (I.fmat x)) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        pm u (I.fmat x) = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rw [cT_pm _ hσ]
    exact pm_form hu _ _ _ hx⟩


theorem smul_Lf {u : I.E ⊗[I.F] Af I.F} (hI : u ∈ IntAf I.F I.E) {y : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hy : y ∈ I.Lf) : u • y ∈ I.Lf :=
  I.Lf.smul_mem ⟨u, hI⟩ hy





end Inst

end Formalism.L2.SG.Pf.AllRowsKCRT
