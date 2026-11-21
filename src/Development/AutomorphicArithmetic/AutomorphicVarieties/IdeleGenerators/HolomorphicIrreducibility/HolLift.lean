import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DelSerre
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExistsIdele
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.FinOfKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpInj

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

variable {F : Type} [Field F] [NumberField F]



private abbrev Idx (F : Type) [Field F] : Type := {𝔪 : Ideal (𝓞 F) // 𝔪 ≠ ⊥}

open Classical in

private def fT {K : Type} [Field K] (w : Pl F) (e : K) : Module.End K (Idx F → K) where
  toFun v 𝔪 := v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0
  map_add' c d := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;> simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.add_apply] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;>
      simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

open Classical in
omit [NumberField F] in
private theorem fT_apply {K : Type} [Field K] (w : Pl F) (e : K) (v : Idx F → K) (𝔪 : Idx F) :
    fT w e v 𝔪 = v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0 := rfl

variable [IsTotallyReal F]

private def SS (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) : Submodule ℂ (TR.Sm F 2) where
  carrier := {φ | IsHol k c ω φ ∧ ∃ c₀ a, HasExp φ.1 k c₀ a}
  zero_mem' := ⟨(holLin F k c ω).1, _, _, (holLin F k c ω).2.1⟩
  add_mem' := by
    rintro φ ψ ⟨h1, c₀, a, h2⟩ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 φ ψ 1 h1 h3
    have e2 := (holLin F k c ω).2.2.2.1 φ.1 ψ.1 1 _ _ _ _ h2 h4
    rw [one_smul] at e1 e2
    exact ⟨e1, _, _, e2⟩
  smul_mem' := by
    rintro z ψ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 0 ψ z (holLin F k c ω).1 h3
    have e2 := (holLin F k c ω).2.2.2.1 0 ψ.1 z _ _ _ _ (holLin F k c ω).2.1 h4
    rw [zero_add] at e1 e2
    exact ⟨e1, _, _, e2⟩

private def cf {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : Ideal (𝓞 F) → ℂ := φ.2.2.choose_spec.choose

private theorem cf_spec {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : ∃ c₀, HasExp φ.1.1 k c₀ (cf φ) :=
  ⟨_, φ.2.2.choose_spec.choose_spec⟩

private theorem cf_eq {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a} (h : HasExp φ.1.1 k c₀ a) (𝔪 : Idx F) :
    cf φ 𝔪.1 = a 𝔪.1 := by
  obtain ⟨d, hd⟩ := cf_spec φ
  exact (expUnique F _ k _ _ _ _ hd h).2 _ 𝔪.2

private def Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) :
    SS k c ω →ₛₗ[(ι.symm : ℂ →+* Qbar l)] (Idx F → Qbar l) where
  toFun φ 𝔪 := ι.symm (cf φ 𝔪.1)
  map_add' φ ψ := by
    funext 𝔪
    obtain ⟨_, h2⟩ := cf_spec φ
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 _ _ 1 _ _ _ _ h2 h4
    simp only [one_smul] at e2
    rw [cf_eq (φ + ψ) e2]
    simp
  map_smul' z ψ := by
    funext 𝔪
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 0 _ z _ _ _ _ (holLin F k c ω).2.1 h4
    simp only [zero_add] at e2
    rw [cf_eq (z • ψ) e2]
    simp



private def hkS {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F} (hω : IsOfFinOrder ω) (w : Pl F) (φ : SS k c ω) : SS k c ω :=
  ⟨hk k w (c w) φ.1, (holHk F k hk1 c ω hω φ.1 φ.2.1 w).1, by
    obtain ⟨_, h⟩ := cf_spec φ
    obtain ⟨d, hd⟩ := (holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h
    exact ⟨d, _, hd⟩⟩



end UpperTheory.V.Sd
