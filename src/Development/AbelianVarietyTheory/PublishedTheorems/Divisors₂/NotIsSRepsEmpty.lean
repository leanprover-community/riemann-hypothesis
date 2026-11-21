import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PosOfTorusNoLe
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusNoLeClassNoRankOne

noncomputable section

namespace GlobalTheory.SUVol.TamModel

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.UCls.Model GlobalTheory.SUVol
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Up.Definite
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sEquiv_refl (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ) (g) : SEquiv G L M g g :=
  ⟨1, by rw [SUVol.ratM_one]; exact ⟨(isKM_one _ G L M).1, det_one⟩, 1, isKM_one _ G L M, det_one, by
    rw [SUVol.ratM_one]; simp⟩

theorem sEquiv_trans {G : Matrix (Fin r) (Fin r) E} {L : Set (Fin r → E)} {M : ℕ} {a b d}
    (h : SEquiv G L M a b) (h' : SEquiv G L M b d) : SEquiv G L M a d := by
  obtain ⟨γ, hγ, k, hk, hd, rfl⟩ := h
  obtain ⟨γ', hγ', k', hk', hd', rfl⟩ := h'
  exact ⟨γ' * γ, by
    rw [SUVol.ratM_mul]; exact ⟨isUA_mul _ G hγ'.1 hγ.1, by rw [det_mul, hγ'.2, hγ.2, one_mul]⟩,
    k * k', isKM_mul _ G L M hk hk', by rw [det_mul, hd, hd', one_mul], by
    rw [SUVol.ratM_mul]; simp only [Matrix.mul_assoc]⟩

theorem sEquiv_symm {G : Matrix (Fin r) (Fin r) E} {L : Set (Fin r → E)} {M : ℕ} {a b}
    (h : SEquiv G L M a b) : SEquiv G L M b a := by
  obtain ⟨γ, hγ, k, hk, hkd, rfl⟩ := h
  have hd1 : γ.det = 1 := by
    have h1 := hγ.2
    rw [ratM_det] at h1
    exact one_tmul_injective (F := maximalRealSubfield E) h1
  have hd : IsUnit γ.det := hd1 ▸ isUnit_one
  have hi : ratM (maximalRealSubfield E) γ⁻¹ * ratM (maximalRealSubfield E) γ = 1 := by
    rw [← SUVol.ratM_mul, nonsing_inv_mul γ hd, SUVol.ratM_one]
  refine ⟨γ⁻¹, ⟨by rw [← inv_eq_left_inv hi]; exact isUA_inv _ G hγ.1, ?_⟩, k⁻¹, isKM_inv _ G L M hk, ?_, ?_⟩
  · have := congrArg det hi
    rwa [det_mul, hγ.2, mul_one, det_one] at this
  · have := congrArg det (nonsing_inv_mul k hk.1.1)
    rwa [det_mul, hkd, mul_one, det_one] at this
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv k hk.1.1, Matrix.mul_one, ← Matrix.mul_assoc, hi,
      Matrix.one_mul]

theorem exists_sReps (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ) :
    ∃ (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), Nonempty J ∧ IsSReps G L M s := by
  let S : Setoid {g // IsSA G g} :=
    ⟨fun a b => SEquiv G L M a.1 b.1, fun a => sEquiv_refl G L M a.1, sEquiv_symm, sEquiv_trans⟩
  refine ⟨Quotient S, fun q => q.out.1, ⟨Quotient.mk S ⟨1, (isKM_one _ G L M).1, det_one⟩⟩, fun q => q.out.2,
    fun i j h => ?_, fun g hg => ⟨Quotient.mk S ⟨g, hg⟩, Quotient.mk_out (s := S) ⟨g, hg⟩⟩⟩
  rw [← i.out_eq, ← j.out_eq]
  exact Quotient.sound h


variable (E) in

theorem exists_cmType : ∃ Ψ : Finset (E →+* ℂ), ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  classical
  refine ⟨Finset.univ.filter fun τ => τ = (InfinitePlace.mk τ).embedding, fun τ => ?_⟩
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h <;> rw [h] <;> simp [hne, hne.symm]

variable (E) in

theorem exists_skew : ∃ δ : E, δ ≠ 0 ∧ IsIntegral ℤ δ ∧ cc δ = -δ := by
  by_contra hcon
  push Not at hcon
  have key : ∀ x : 𝓞 E, cc (x : E) = x := fun x => by
    by_contra hx
    refine hcon ((x : E) - cc (x : E)) (sub_ne_zero.2 (Ne.symm hx)) (x.isIntegral_coe.sub (isIntegral_cc x.isIntegral_coe)) ?_
    simp [cc]
  apply IsCMField.complexConj_ne_one E
  ext y
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have ha := key a
  have hb' := key b
  simp only [cc] at ha hb'
  simp only [map_div₀, AlgEquiv.one_apply]
  exact congrArg₂ (· / ·) ha hb'




theorem mem_ratStab_of (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (s k) (γ : GL (Fin r) E)
    (h1 : (γ : Matrix (Fin r) (Fin r) E).det = 1)
    (h2 : ∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y)
    (hk : IsKM (IsCMField.complexConj E) G L 1 k)
    (he : ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) * s = s * k) : γ ∈ ratStab G L s := by
  refine ⟨h1, h2, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨z, hz, rfl⟩ := hk.2.2 y hy
    refine ⟨z, hz, ?_⟩
    have hi : ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
        ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) = 1 := by
      rw [← SUVol.ratM_mul, Units.inv_mul, SUVol.ratM_one]
    have := congrArg (ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ·) hxy
    simp only [mulVec_mulVec] at this
    rwa [← he, ← Matrix.mul_assoc, hi, Matrix.one_mul, one_mulVec] at this
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k *ᵥ y, IsKM_maps _ G L 1 hk hy, by rw [mulVec_mulVec, mulVec_mulVec, he]⟩

end GlobalTheory.SUVol.TamModel
