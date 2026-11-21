import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.HostUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Number

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia
open IsDedekindDomain

open UpperTheory.V.Af in
private def NB (K : Type) [Field K] [NumberField K] [IsCMField K] (c A : ℕ) : Prop :=
    ∀ e : ℕ, 1 ≤ e → ∀ N : ℕ, 1 ≤ N → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → 7 ≤ p →
      ¬ p ∣ N → ¬ (p : ℤ) ∣ discr K →
    ∀ (Orb : Type) [Fintype Orb] (z : Orb → ℂ), (∀ o, ∃ k : ℕ, 0 < k ∧ z o ^ k = 1) →
      (∀ σ : ℂ ≃+* ℂ, ∃ u : Orb ≃ Orb, ∀ o, z (u o) = σ (z o)) →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c * Fintype.card Orb * ((N : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
        [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), IsPlaceOver B w →
        ∀ σ : Formalism.ConjugateSelfDual.G K Ω, IsFrob B (normV w) σ →
        ∀ X : Orb → Finset (Formalism.ConjugateSelfDual.G K Ω →* GL (Fin 3) (Qbar l)),
          (∀ o, ∀ ρ ∈ X o, UpperTheory.V.Z.J.Adm3U ι e N ρ ∨ Adm2 ι e (N * (discr K).natAbs) ρ) →
          (∀ o, ∀ ρ ∈ X o, ∀ ρ' ∈ X o, RepIso ρ ρ' → ρ = ρ') →
          (∀ o, ∀ ρ ∈ X o, (ρ σ⁻¹ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ ι.symm (eis3 (normV w) e (z o))) ∧
          ‖((NN : ℤ) : Qbar l)‖ ≤
            ∏ o, ∏ ρ ∈ X o, ‖(ρ σ⁻¹ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 (normV w) e (z o))‖







section Host

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N]
  {e : ℕ} {ψ : DirichletCharacter c.O N} {o₁ : ℕ} {S : Finset Pl} {A : S → ValuationSubring Ω}
  {F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S}

private theorem algClosure (K Ω : Type) [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    [IsScalarTower ℚ K Ω] : IsAlgClosure K Ω :=
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩



variable {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsScalarTower ℚ K Ω]

omit [IsCMField K] in
private theorem ker_lift (hK : IsQi K) (hF : IsHostFrame Ω c e ψ S A F) {g : Gam Ω S} (hg : g ∈ F.η.ker) :
    ∃ s : Formalism.ConjugateSelfDual.G K Ω, toGS Ω _ (s.restrictScalars ℚ) = g := by
  obtain ⟨σ, rfl⟩ : ∃ σ, toGS Ω (S : Set Pl) σ = g := QuotientGroup.mk_surjective g
  have h : σ ∈ (eta4 Ω).ker := by
    rw [← hF.η, hF.π]
    exact hg
  rw [← (gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1] at h
  obtain ⟨s, rfl⟩ := h
  exact ⟨s, rfl⟩



omit [IsCMField K] in
private theorem exists_w {p : ℕ} (hp : p.Prime) {B : ValuationSubring Ω} (hB : B.valuation (p : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver B w ∧ (p : 𝓞 K) ∈ w.asIdeal := by
  haveI := algClosure K Ω
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.Base.places K Ω p B
  obtain ⟨w, hw⟩ := h1 fun h => (h2 h).2 hB
  exact ⟨w, hw, (h3 w hw).1 hB⟩


end Host


open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th UpperTheory.V.Z.J

