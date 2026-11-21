import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.EqOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem det_mem_Uo (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {g : Matrix.GeneralLinearGroup Unit k} (hg : g ∈ KO k Unit) :
    Matrix.GeneralLinearGroup.det g ∈ UpperTheory.V.Hi.Uo k := by
  obtain ⟨h, rfl⟩ := hg
  show valuation k ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h) : kˣ) : k) = 1
  rw [Matrix.GeneralLinearGroup.map_det]
  exact (Valuation.integer.integers (valuation k)).valuation_unit _

theorem UpperTheory.V.Z.Sym.Al.locSph :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, ∀ u ∈ Hi.Uo k, ψ i u = 1) → ∃ v, v ≠ 0 ∧ ∀ u ∈ KO k (Fin n), prinSeries ψ u v = v := by
  intro k _ _ _ _ n ψ hψ
  have key : ∀ g : Levi k (fun _ : Fin n => Unit), (∀ a, g a ∈ KO k Unit) →
      (MonoidHom.comp (ofChar (torusChar ψ)) (leviTorus k (Fin n)).symm.toMonoidHom) g (1 : ℂ) = 1 := by
    intro g hg
    have hs : (leviTorus k (Fin n)).symm g = fun i => Matrix.GeneralLinearGroup.det (g i) := rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ofChar_apply, hs, torusChar_apply]
    rw [Finset.prod_eq_one fun i _ => hψ i _ (det_mem_Uo k (hg i))]
    simp
  obtain ⟨f, hf, h1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (points (Fin n)) key
  refine ⟨f, ?_, fun u hu => GlobalTheory.LGrp.mem_fixed.mp hf u hu⟩
  rintro rfl
  simp at h1
end

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.sph :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : Submodule ℂ (UA L n → ℂ)) (w : Plc L) (ψ : Fin n → (Kw w)ˣ →* ℂˣ), IsSplitAt w → CompSub π w ψ →
                 (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) → (∀ i i', i ≠ i' → ψ i ≠ ψ i' ∧ ψ i ≠ ψ i' * absPow (Kw w) 1) → IsUnramU π w := by
  intro H L _ _ _ n π w ψ hw hc hu hne
  obtain ⟨hsm, τ, ⟨-, f, hf0, hfπ, hf⟩, hsq⟩ := hc
  obtain ⟨hs1, hs2, -, -⟩ := secSpec L n w hw

  have hker : ∀ x, f x = 0 → x = 0 := by
    let S : Subrepresentation τ.ρ := ⟨LinearMap.ker f, by
      intro g x hx
      have h := hf ⟨secW n w g, hs1 g⟩ x
      have h' : f (τ.ρ g x) = RU L n (secW n w g) (f x) := by
        rw [← h]
        show f (τ.ρ g x) = f (τ.ρ (cLoc w (secW n w g)) x)
        rw [hs2 g]
      rw [LinearMap.mem_ker] at hx ⊢
      rw [h', hx, map_zero]⟩
    have hS : S = ⊥ := by
      rcases (τ.irred.eq_bot_or_eq_top S) with h | h
      · exact h
      · refine absurd (LinearMap.ext fun x => ?_) hf0
        have : x ∈ S.toSubmodule := by rw [h]; trivial
        exact this
    intro x hx
    have : x ∈ S.toSubmodule := hx
    rw [hS] at this
    exact this

  obtain ⟨ω, rfl, hω⟩ : ∃ ω : Fin n → (Kw w)ˣ →* ℂˣ,
      ψ = (fun i => ω i * absPow (Kw w) (((n : ℂ) - 1) / 2)) ∧ ∀ i, IsSmoothChar (ω i) := by
    refine ⟨fun i => ψ i * absPow (Kw w) (-(((n : ℂ) - 1) / 2)), funext fun i => ?_,
      fun i => (hsm i).mul (isSmoothChar_of_isUnram (isUnram_absPow _ _))⟩
    have h0 : absPow (Kw w) 0 = 1 := by
      ext x
      simp [absPow]
    rw [mul_assoc, ← absPow_add, neg_add_cancel, h0, mul_one]
  have hneω : ∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow (Kw w) 1 := fun i j hij =>
    ⟨fun h => (hne i j hij).1 (by simp only [h]), fun h => (hne i j hij).2 (by
      simp only []
      rw [h, mul_right_comm])⟩
  obtain ⟨E⟩ := (Hi.psIrr H (Kw w) n ω hω hneω).2 _ τ.ρ τ.irred hsq
  obtain ⟨v₀, hv₀, hfix⟩ := locSph (Kw w) n _ hu
  obtain ⟨v, rfl⟩ := E.surjective v₀
  have hv : v ≠ 0 := by
    rintro rfl
    exact hv₀ (map_zero E)
  have hτ : ∀ u ∈ KO (Kw w) (Fin n), τ.ρ u v = v := fun u hu' => by
    apply E.injective
    have h1 := LinearMap.congr_fun (E.isIntertwining' u) v
    exact h1.trans (hfix u hu')
  refine ⟨f v, hfπ v, fun h => hv (hker v h), fun x hx hK => ?_⟩
  have h := hf ⟨x, hx⟩ v
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL] at hK
  rw [← h]
  show f (τ.ρ (cLoc w x) v) = f v
  rw [hτ _ hK]
end
