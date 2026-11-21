import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSumTwistCompat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsExtensionUniqueOnCuspidal

section
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL

theorem isL_map_tw_of_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  intro k _ _ _ _ _ 𝔪 x χ hχ h
  exact (h.tw χ hχ).of_equiv (x.twEquiv χ hχ)

end GlobalTheory.LocGL
end

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLanglandsClassification_twist_multisegment : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  atlas_forward_decl GlobalTheory.LocGL.isL_map_tw_of_isL
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_sum_twist_compat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l l' : List (WD h), l.Perm l' → sumList l = sumList l') ∧ (∀ (l : List (WD h)) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (sumList l).lpTwist ξ hξ = sumList (l.map fun y => y.lpTwist ξ hξ)) ∧ (∀ (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) ∧ (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y) ∧ (∀ (x : WD h) (l : List (WD h)), x.lpChar (sumList l) = sumList (l.map x.lpChar)) ∧ (∀ l : List (WD h), (sumList l).lpDim = (l.map WD.lpDim).sum ∧ ∀ σ, (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod) := by
  first | exact @GlobalTheory.sumList_laws | exact GlobalTheory.sumList_laws | (intros; apply GlobalTheory.sumList_laws <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.ExtTwist

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpTwist_comm (x : WD h) (ξ η : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ)
    (hη : WeilDeligne.IsSmooth η) : (x.lpTwist ξ hξ).lpTwist η hη = (x.lpTwist η hη).lpTwist ξ hξ := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  simp only [WD.lpTwist_mk]
  exact WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => smul_comm (η σ : ℂ) (ξ σ : ℂ) (b.ρ σ v), fun v => rfl⟩

theorem hasCentralChar_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : HasCentralChar (IrrGL.ofChar χ hχ).rep χ := fun z v => by
  let φ := equivRep (IrrRep.det (Fin 1) χ hχ)
  obtain ⟨u, rfl⟩ := φ.toLinearEquiv.surjective v
  have h2 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z := by
    ext; simp [GeneralLinearGroup.scalar]
  have h3 : (IrrRep.det (Fin 1) χ hχ).ρ (GeneralLinearGroup.scalar (Fin 1) z) u = (χ z : ℂ) • u := by
    show (χ (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z)) : ℂ) • u = _
    rw [h2]
  show (IrrRep.det (Fin 1) χ hχ).cl.rep.ρ (GeneralLinearGroup.scalar (Fin 1) z) (φ.toIntertwiningMap u) =
    _ • φ.toIntertwiningMap u
  rw [← φ.toIntertwiningMap.isIntertwining, h3, map_smul]
  rfl

end GlobalTheory.LocLanglands.ExtTwist

end
end
