import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.SegmentV
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsSumMultiplicityOne
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne
namespace GlobalTheory.Published
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  {𝔪 𝔫 : Multiset (Segment k)} {r t : ℕ} {π₁ : IrrRep (GL (Fin r) k)} {π₂ : IrrRep (GL (Fin t) k)}
end GlobalTheory.Published
namespace GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h}
abbrev _root_.GlobalTheory.LocLanglands.IsRec.langlandsQuotient_s_ty : Prop := ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h} (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {𝔪 : Multiset (Segment (w.adicCompletion E))} {s N : ℕ}
    {δ : Fin s → IrrGL (w.adicCompletion E)} (hδ : LFactors 𝔪 δ) (hd : ∑ i, (δ i).1 = N)
    {π : IrrRep (GL (Fin N) (w.adicCompletion E))} (hπ : IsCosocle π.ρ (prodIrr δ hd)),
    rc (cls π) = sumList (List.ofFn fun i => rc (δ i))
end GlobalTheory.LocLanglands
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.T2
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h}
private theorem segmentV {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
    (H : LawsV a ha ε rc) {Δ : Segment (w.adicCompletion E)} {x : IrrGL (w.adicCompletion E)}
    (hx : IsLSeg Δ x.rep) :
    rc x = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len) :=
  (H.langlands [Δ] x hx.isL).trans (WD.lpSum_zero _)
end UpperTheory.V.Z.Win.T2
theorem UpperTheory.V.Z.Win.T2.lQuot_alt :
    _root_.GlobalTheory.LocLanglands.IsRec.langlandsQuotient_s_ty := by
  intro E Ω i₁ i₂ i₃ i₄ i₅ A w h rc hrc 𝔪 s N δ hδ hd π hπ
  have h1 : IsL 𝔪 (GlobalTheory.LocLanglands.cls π).rep := IsL.of_equiv ⟨s, δ, hd, hδ, hπ⟩ (equivRep π)
  obtain ⟨Δ, ⟨hm, -⟩, hΔ⟩ := hδ
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  simp only [fun i => UpperTheory.V.Z.Win.T2.segmentV H (hΔ i)]
  rw [H.langlands (List.ofFn Δ) (GlobalTheory.LocLanglands.cls π) (by rwa [← Fin.univ_val_map, hm]), List.map_ofFn]
  rfl
end
end
end
