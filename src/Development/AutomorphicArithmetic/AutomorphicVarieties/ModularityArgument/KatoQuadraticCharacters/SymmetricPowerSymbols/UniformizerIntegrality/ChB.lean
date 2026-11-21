import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec

section
noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

namespace UpperTheory.V.Z.Kato.Sym.PT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

attribute [local instance] algMdl

private theorem e_model (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) (f : topF X M) :
    e (algebraMap (topF X M) (topBar X M) f) = io X f := by
  rw [IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M) f]
  exact he _

private theorem cj_spec (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) (σ : RingAut (Kb X))
    (hσ : FixF X M σ) (z : topBar X M) : e (cj X M e σ z) = σ (e z) := by
  have hex : ∃ g : topGal X M, ∀ z, e (g z) = σ (e z) := by
    refine ⟨AlgEquiv.ofRingEquiv (f := e.trans (σ.trans e.symm)) ?_, ?_⟩
    · intro f
      simp only [RingEquiv.trans_apply]
      rw [e_model X M e he f, hσ f f.2, ← e_model X M e he f, RingEquiv.symm_apply_apply]
    · intro w
      simp [AlgEquiv.ofRingEquiv_apply]
  exact Classical.epsilon_spec (p := fun g : topGal X M => ∀ w, e (g w) = σ (e w)) hex z

private theorem fix_mul (X : Tower Ω ε) (M : ℕ) {σ τ : RingAut (Kb X)} (hσ : FixF X M σ) (hτ : FixF X M τ) :
    FixF X M (σ * τ) := fun f hf => by
  show σ (τ (io X f)) = io X f
  rw [hτ f hf, hσ f hf]

private theorem fix_inv (X : Tower Ω ε) (M : ℕ) {σ : RingAut (Kb X)} (hσ : FixF X M σ) : FixF X M σ⁻¹ := fun f hf => by
  show σ.symm (io X f) = io X f
  rw [RingEquiv.symm_apply_eq]
  exact (hσ f hf).symm

private theorem cj_mul (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) {σ τ : RingAut (Kb X)}
    (hσ : FixF X M σ) (hτ : FixF X M τ) : cj X M e (σ * τ) = cj X M e σ * cj X M e τ := by
  ext z
  apply e.injective
  rw [cj_spec X M e he _ (fix_mul X M hσ hτ), AlgEquiv.mul_apply, cj_spec X M e he _ hσ, cj_spec X M e he _ hτ]
  rfl

private theorem cj_one (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) :
    cj X M e 1 = 1 := by
  ext z
  apply e.injective
  rw [cj_spec X M e he _ (fun f _ => rfl)]
  rfl

private theorem cj_inv (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) {σ : RingAut (Kb X)}
    (hσ : FixF X M σ) : cj X M e σ⁻¹ = (cj X M e σ)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← cj_mul X M e he (fix_inv X M hσ) hσ, inv_mul_cancel, cj_one X M e he]

private theorem e_zeta (X : Tower Ω ε) (M : ℕ) (e : topBar X M ≃+* Kb X) (he : IsIso X M e) (l n : ℕ) :
    e (topZeta X M l n) = zt X (l ^ n) := by
  unfold topZeta zt
  rw [he]
  push_cast
  rfl

theorem cjB : CjB := by
  intro Ω _ _ _ ε X M e he
  refine ⟨fun σ hσ z => cj_spec X M e he σ hσ z, fun σ τ hσ hτ =>
    ⟨fix_mul X M hσ hτ, fix_inv X M hσ, cj_mul X M e he hσ hτ, cj_inv X M e he hσ⟩, fun σ hσ => ?_,
    fun l n => e_zeta X M e he l n, ?_⟩
  · have hF : FixF X M σ := fun f hf => hσ f (mdl_le_lev X _ _ hf)
    have key : ∀ f : topL X M, cj X M e σ (algebraMap (topL X M) (topBar X M) f) = algebraMap (topL X M) (topBar X M) f := by
      intro f
      apply e.injective
      rw [cj_spec X M e he σ hF, he]
      exact hσ _ f.2
    refine ⟨hF, ?_⟩
    rintro ⟨_, f, rfl⟩
    exact key f
  · intro l n hl σ _ a b hb i hab
    have hm : 0 < l ^ n := pow_pos (Nat.pos_of_ne_zero hl) n
    refine (lgB Ω ε X (l ^ n) hm).2.2.1 (e a) (e b) i (by simpa using hb) ?_
    rw [hab, map_mul, map_pow, e_zeta X M e he l n]

end UpperTheory.V.Z.Kato.Sym.PT

end
end

section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

theorem UpperTheory.V.Z.Kato.Sym.PT.chB : UpperTheory.V.Z.Kato.Sym.PT.ChB := by
  intro Ω _ _ _ ε X l n M hl hM hdvd u hu0 huF e he
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hN : l ^ n ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ n) := ⟨hN⟩
  have huL : u ∈ topL X M := mdl_le_lev X _ _ huF
  have hpow := topRoot_pow X M hN huL
  have h1 : e (topRoot X M (l ^ n) u) ^ l ^ n = io X u := by
    rw [← map_pow, hpow]
    exact he ⟨u, huL⟩
  refine ⟨h1, ?_⟩
  intro σ hσ
  obtain ⟨hc1, -, -, -, hlg⟩ := cjB Ω ε X M e he
  have hθ0 : topRoot X M (l ^ n) u ≠ 0 := by
    intro h
    rw [h, zero_pow hN] at hpow
    apply hu0
    have h2 : (⟨u, huL⟩ : topL X M) = 0 :=
      (algebraMap (topL X M) (topBar X M)).injective (hpow.symm.trans (map_zero _).symm)
    exact congrArg Subtype.val h2
  have hfix : cj X M e σ (topRoot X M (l ^ n) u ^ l ^ n) = topRoot X M (l ^ n) u ^ l ^ n := by
    rw [hpow]
    have h3 : (algebraMap (topL X M) (topBar X M)) ⟨u, huL⟩
        = algebraMap (topF X M) (topBar X M) ⟨u, huF⟩ := by
      rw [IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]
      rfl
    rw [h3]
    exact (cj X M e σ).commutes _
  have hζ := isPrimitiveRoot_topZeta X M hl.ne_zero n
  have hr : (cj X M e σ (topRoot X M (l ^ n) u) * (topRoot X M (l ^ n) u)⁻¹) ^ l ^ n = 1 := by
    rw [mul_pow, inv_pow, ← map_pow, hfix]
    exact mul_inv_cancel₀ (pow_ne_zero _ hθ0)
  obtain ⟨k, hk, hkr⟩ := hζ.eq_pow_of_pow_eq_one hr
  have hex : ∃ i : ZMod (l ^ n),
      cj X M e σ (topRoot X M (l ^ n) u) = topZeta X M l n ^ i.val * topRoot X M (l ^ n) u := by
    refine ⟨(k : ZMod (l ^ n)), ?_⟩
    rw [ZMod.val_natCast_of_lt hk, hkr, inv_mul_cancel_right₀ hθ0]
  rw [topChar_apply X hl.ne_zero hdvd huF hu0 (cj X M e σ)]
  show lg X (l ^ n) (σ (e (topRoot X M (l ^ n) u))) (e (topRoot X M (l ^ n) u)) = _
  rw [← hc1 σ hσ]
  apply hlg l n hl.ne_zero σ hσ _ _ hθ0
  simp only [GlobalTheory.NeedB.kum, dif_pos hex]
  exact hex.choose_spec
end
