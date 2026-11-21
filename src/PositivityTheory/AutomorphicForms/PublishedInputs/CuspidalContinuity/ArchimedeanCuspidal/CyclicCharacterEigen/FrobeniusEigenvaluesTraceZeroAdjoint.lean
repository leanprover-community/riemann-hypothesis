import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SelfTwGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Sd.EG

namespace Ad3P.SEGAux

theorem adjoint_zero_twist {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (χ : Γ →* kˣ) : ad0 (tw ρ χ) = ad0 ρ := by
  have hv : ∀ (ρ' : Γ →* GL (Fin 2) k) (s : Γ), (ad0 ρ' s : Matrix (Fin 3) (Fin 3) k) =
      ((ρ' s : Matrix (Fin 2) (Fin 2) k).det)⁻¹ • symSquareMatrixHom k (ρ' s : Matrix (Fin 2) (Fin 2) k) := fun ρ' s => by
    rw [ad0, tw_val]
    simp
  ext s : 1
  apply Units.ext
  rw [hv, hv, tw_val, Matrix.det_smul, Fintype.card_fin]
  have hc : (χ s : k) ≠ 0 := (χ s).ne_zero
  have hd : (ρ s : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := (ρ s).det_ne_zero
  have e : symSquareMatrixHom k ((χ s : k) • (ρ s : Matrix (Fin 2) (Fin 2) k)) = (χ s : k) ^ 2 • symSquareMatrixHom k (ρ s : Matrix (Fin 2) (Fin 2) k) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom] <;> ring
  rw [e, smul_smul]
  congr 1
  field_simp


private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem charEig_cyc_inv {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    CharEig ι (cycBar F Ω l)⁻¹ w (normV w : ℂ) := by
  intro A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ F Ω l s = 1 := Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
      rw [cycZ_toZModPow_eq hw hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp)
    rw [MonoidHom.inv_apply, cycBar, MonoidHom.comp_apply, h1, map_one, inv_one]
  · have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
    rw [MonoidHom.inv_apply, map_inv, inv_inv, h2, map_natCast]

private theorem frobenius_eigenvalues_trace_zero_adjoint {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ρ : G F Ω →* GL (Fin 2) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (a b : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : FrobEig ι ρ w {a, b}) : FrobEig ι (ad0 ρ) w {a / b, 1, b / a} := by
  intro A hA
  obtain ⟨h1, h2⟩ := h A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · apply Units.ext
    rw [ad0, tw_val, MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h1 s hs]
    simp
  · have ha' : ι.symm a ≠ 0 := by simpa using ha
    have hb' : ι.symm b ≠ 0 := by simpa using hb
    have h3 : (ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
        (X - C ((Units.mk0 _ ha' : (Qbar l)ˣ) : Qbar l)) * (X - C ((Units.mk0 _ hb' : (Qbar l)ˣ) : Qbar l)) := by
      apply Polynomial.map_injective ι.toRingHom ι.injective
      rw [h2 σ hσ]
      simp
    rw [(UpperTheory.V.Sd.ad0Facts l (G F Ω) ρ).2.2.2.2.1 _ _ _ h3]
    simp [mul_assoc]



section Norm

variable {l : ℕ} [hl : Fact l.Prime]


variable (l) in

private def Uprin : Subgroup (Qbar l)ˣ where
  carrier := {u | ‖(u : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have e : ((u * v : (Qbar l)ˣ) : Qbar l) - 1 = u * (v - 1) + (u - 1) := by push_cast; ring
    show ‖_‖ < 1
    rw [e]
    refine small_add ?_ hu
    rw [norm_mul, norm_eq_one_of hu, one_mul]
    exact hv
  inv_mem' {u} hu := by
    have e : (u : Qbar l) * (((u⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(u - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, norm_eq_one_of hu, one_mul, norm_neg] at this
    show ‖_‖ < 1
    rw [this]
    exact hu




end Norm

section Gal

variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]







end Gal

end Ad3P.SEGAux
