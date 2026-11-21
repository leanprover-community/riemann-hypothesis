import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.LocM.TorCheck


variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem minVal_eval (B : X → X → ℝ) : (InvFun.minVal O).eval X B = sInf {x | (∃ y, B y y = x) ∧ x ≠ B 0 0} := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr]
  change sInf _ = _
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, map_zero]
  exact and_congr_left' ⟨fun ⟨y, h⟩ => ⟨r y, h⟩, fun ⟨y, h⟩ => (hr y).elim fun z e => ⟨z, e ▸ h⟩⟩

theorem minVal_linearOn (γ : LinearMap.BilinForm ℤ X) : (InvFun.minVal O).LinearOn ![γ] := by
  intro c hc
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, InvFun.evalZ, minVal_eval, map_zero, Int.cast_zero, mul_zero,
    LinearMap.zero_apply]
  rcases (hc 0).eq_or_lt with h | h
  · rw [← h]
    simp only [zero_mul]
    convert Real.sInf_empty
    exact Set.eq_empty_of_forall_notMem fun x ⟨⟨_, h⟩, h'⟩ => h' h.symm
  · rw [← smul_eq_mul (c 0) (sInf _), ← Real.sInf_smul_of_nonneg (hc 0)]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨⟨y, rfl⟩, hx⟩
      exact ⟨_, ⟨⟨y, rfl⟩, fun e => hx (by rw [e, mul_zero])⟩, rfl⟩
    · rintro ⟨_, ⟨⟨y, rfl⟩, hx⟩, rfl⟩
      exact ⟨⟨y, rfl⟩, mul_ne_zero h.ne' hx⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem eq_zero_of_apply_self {β : LinearMap.BilinForm ℤ (𝓞 E)} (hβ : β ∈ levelForms H 1 (𝓞 E))
    (hp : ∀ y, 0 ≤ β y y) {y₀ : 𝓞 E} (hy : y₀ ≠ 0) (h : β y₀ y₀ = 0) (y : 𝓞 E) : β y y = 0 := by
  have h1 : ∀ z, β y₀ z = 0 := fun z => by
    by_contra hz
    have k := hp ((-(β z z + 1) * β y₀ z) • y₀ + z)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h, hβ.1 z y₀] at k
    have : 1 ≤ β y₀ z * β y₀ z := mul_self_pos.2 hz
    have := hp z
    nlinarith
  obtain ⟨N, hN, c, hc⟩ : ∃ N : ℤ, N ≠ 0 ∧ ∃ c : 𝓞 E, c * y₀ = N := by
    have hI : Ideal.span {y₀} ≠ ⊥ := by simpa using hy
    refine ⟨(Ideal.absNorm (Ideal.span {y₀}) : ℕ), ?_, ?_⟩
    · exact_mod_cast fun e => hI (Ideal.absNorm_eq_zero_iff.1 e)
    · have := Ideal.absNorm_mem (Ideal.span {y₀})
      simpa using Ideal.mem_span_singleton'.1 this
  have h2 : β ((y * c) • y₀) y = 0 := by rw [hβ.2.1, h1]
  have e : (y * c) • y₀ = N • y := by rw [smul_eq_mul, mul_assoc, hc, zsmul_eq_mul, mul_comm]
  rw [e, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left hN


end GlobalTheory.LocM.TorCheck
