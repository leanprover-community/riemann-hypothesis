import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocle
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NonemptyEquivParIndZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEqStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsClassificationOrderFreeEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsInterleaveSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursIrreducibleSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleaveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccurs

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdSubquot
open TensorProduct

section General
variable {G H V V' W W' : Type} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem isSubquotient_extTensor_left {σ : Representation ℂ G V} {σ' : Representation ℂ G V'}
    (B : Representation ℂ H W) (h : IsSubquotient σ σ') :
    IsSubquotient (extTensor σ B) (extTensor σ' B) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap σ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_left B ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapLeft B f) :=
    LinearMap.rTensor_surjective W hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_extTensor_right {ρ : Representation ℂ H W} {ρ' : Representation ℂ H W'}
    (A : Representation ℂ G V) (h : IsSubquotient ρ ρ') :
    IsSubquotient (extTensor A ρ) (extTensor A ρ') := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap ρ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_right A ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapRight A f) :=
    LinearMap.lTensor_surjective V hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_comp {L : Type} [Group L] {σ : Representation ℂ G V}
    {σ' : Representation ℂ G V'} (s : L →* G) (h : IsSubquotient σ σ') :
    IsSubquotient (σ.comp s) (σ'.comp s) := by
  obtain ⟨S, f, hf⟩ := h
  let T : Subrepresentation (σ'.comp s) :=
    ⟨S.toSubmodule, fun x _ hv => S.apply_mem_toSubmodule (s x) hv⟩
  exact ⟨T, ⟨f.toLinearMap, fun x => f.isIntertwining' (s x)⟩, hf⟩

end General

theorem prod₂_isSubquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U U' W W' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U') (ρ : Representation ℂ (GL (Fin t) k) W) (ρ' : Representation ℂ (GL (Fin t) k) W'), IsSmooth σ' → IsSmooth ρ' → IsSubquotient σ σ' → IsSubquotient ρ ρ' → IsSubquotient (prod₂ σ ρ) (prod₂ σ' ρ') := by
  intro k _ _ _ _ r t U U' W W' _ _ _ _ _ _ _ _ σ σ' ρ ρ' hσ' hρ' hs hr
  have hext : IsSubquotient (extTensor σ ρ) (extTensor σ' ρ') :=
    (isSubquotient_extTensor_left ρ hs).trans (isSubquotient_extTensor_right σ' hr)
  have hsm : IsSmooth ((extTensor σ' ρ').comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor hσ' hρ') _
      (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
        (continuous_apply false).prodMk (continuous_apply true))
  exact GlobalTheory.ParIndSubquot.parInd_isSubquotient k _ _ _ _ _ _ _ _ hsm
    (isSubquotient_comp _ hext)

end GlobalTheory.CompanionTheory.ProdSubquot
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.Ysupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSubquotient_of_prod₂_equiv {r t : ℕ} {U W A B C D : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    [AddCommGroup D] [Module ℂ D] {σ : Representation ℂ (GL (Fin r) k) U} {ρ : Representation ℂ (GL (Fin t) k) W}
    {α : Representation ℂ (GL (Fin r) k) A} {β : Representation ℂ (GL (Fin t) k) B}
    {γ : Representation ℂ (GL (Fin (r + t)) k) C} {δ : Representation ℂ (GL (Fin (r + t)) k) D}
    (hα : IsSmooth α) (hβ : IsSmooth β) (h₁ : IsSubquotient σ α) (h₂ : IsSubquotient ρ β)
    (E : (prod₂ σ ρ).Equiv δ) (F : (prod₂ α β).Equiv γ) : IsSubquotient δ γ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective).trans
    ((GlobalTheory.CompanionTheory.ProdSubquot.prod₂_isSubquotient k r t U A W B σ α ρ β hα hβ h₁ h₂).trans
      (.of_injective F.toIntertwiningMap F.toLinearEquiv.injective))

theorem nonempty_prod₂_equiv_prodIrr_succ {c : ℕ} (y : Fin (c + 1) → IrrGL k)
    (hd : ∑ a, (y a).1 = (y 0).1 + ∑ a : Fin c, (y a.succ).1) :
    Nonempty ((prod₂ (y 0).rep (prodIrr (fun a : Fin c => y a.succ) rfl)).Equiv (prodIrr y hd)) := by
  have := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := k) (fun a => (y a).1) hd fun a => (y a).rep
  exact this

end GlobalTheory.CompanionTheory.Ysupp
end
end

section
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.LProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLSeg_append {p q : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (Δ₁ : Fin p → Segment k)
    (Δ₂ : Fin q → Segment k) (h₁ : ∀ i, IsLSeg (Δ₁ i) (x i).rep) (h₂ : ∀ i, IsLSeg (Δ₂ i) (y i).rep)
    (i : Fin (p + q)) : IsLSeg (Fin.append Δ₁ Δ₂ i) (Fin.append x y i).rep := by
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left, Fin.append_left]; exact h₁ i
  | right i => rw [Fin.append_right, Fin.append_right]; exact h₂ i

theorem map_append {p q : ℕ} (Δ₁ : Fin p → Segment k) (Δ₂ : Fin q → Segment k) :
    Finset.univ.val.map (Fin.append Δ₁ Δ₂) = Finset.univ.val.map Δ₁ + Finset.univ.val.map Δ₂ := by
  rw [Fin.univ_val_map, Fin.univ_val_map, Fin.univ_val_map, List.ofFn_fin_append]
  rfl

theorem prod₂_isSubquotient_append {r t p q : ℕ} {U W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) U) (ρ : Representation ℂ (GL (Fin t) k) W)
    (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hd : ∑ i, (Fin.append x y i).1 = r + t) (h₁ : IsSubquotient σ (prodIrr x hx))
    (h₂ : IsSubquotient ρ (prodIrr y hy)) : IsSubquotient (prod₂ σ ρ) (prodIrr (Fin.append x y) hd) := by
  obtain ⟨F⟩ := GlobalTheory.T.product_irreducible_append_equiv k p q r t x y hx hy hd
  exact GlobalTheory.CompanionTheory.Ysupp.isSubquotient_of_prod₂_equiv (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)
    h₁ h₂ (Representation.Equiv.refl _) F

end GlobalTheory.CompanionTheory.LProd

theorem GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (a b : IrrGL k), IsL 𝔪 a.rep → IsL 𝔫 b.rep → ∃ (h : ℕ) (z : Fin h → IrrGL k) (Δ : Fin h → Segment k) (hd : ∑ i, (z i).1 = a.1 + b.1), (∀ i, IsLSeg (Δ i) (z i).rep) ∧ Finset.univ.val.map Δ = 𝔪 + 𝔫 ∧ IsSubquotient (prod₂ a.rep b.rep) (prodIrr z hd) := by
  intro k _ _ _ _ _ 𝔪 𝔫 a b ha hb
  obtain ⟨p, x, hx, ⟨Δ₁, hO₁, hL₁⟩, hc₁⟩ := ha
  obtain ⟨q, y, hy, ⟨Δ₂, hO₂, hL₂⟩, hc₂⟩ := hb
  have hd : ∑ i, (Fin.append x y i).1 = a.1 + b.1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hx, hy]
  refine ⟨p + q, Fin.append x y, Fin.append Δ₁ Δ₂, hd, GlobalTheory.CompanionTheory.LProd.isLSeg_append x y Δ₁ Δ₂ hL₁ hL₂, ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.LProd.map_append, hO₁.1, hO₂.1]
  · exact GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_append _ _ x y hx hy hd hc₁.isSubquotient hc₂.isSubquotient

end
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_langlands_subquotient_segments : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (a b : IrrGL k), IsL 𝔪 a.rep → IsL 𝔫 b.rep → ∃ (h : ℕ) (z : Fin h → IrrGL k) (Δ : Fin h → Segment k) (hd : ∑ i, (z i).1 = a.1 + b.1), (∀ i, IsLSeg (Δ i) (z i).rep) ∧ Finset.univ.val.map Δ = 𝔪 + 𝔫 ∧ IsSubquotient (prod₂ a.rep b.rep) (prodIrr z hd) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg
end

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_occurs_irreducible_subquotient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ w : List (IrrGL k), Wd π w → ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ π ∧ Wd τ.ρ w := by
  first | exact @GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd | exact GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd | (intros; apply GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd <;> assumption)
end

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LangSumSub

theorem isL_of_exhaust {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hEx : ∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) {N : ℕ} (τ : IrrRep (GL (Fin N) k)) :
    ∃ 𝔭 : Multiset (Segment k), IsL 𝔭 τ.ρ := by
  obtain ⟨𝔭, h𝔭⟩ := hEx (IrrGL.of τ.ρ τ.smooth τ.irr)
  exact ⟨𝔭, h𝔭.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irr).symm⟩

set_option maxHeartbeats 1000000 in

theorem isSubquotient_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSoc : LSocleGL k)
    (hSeg : LSegJacquet k) (hFree : LOrderFree k) (hEx : ∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep)
    (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1)
    (h0 : IsL 𝔪 (x 0).rep) (h1 : IsL 𝔫 (x 1).rep) (hy : IsL (𝔪 + 𝔫) y.rep) : IsSubquotient y.rep (prodIrr x hd) := by
  obtain ⟨n, c⟩ := y
  obtain rfl : (x 0).1 + (x 1).1 = n := (Fin.sum_univ_two _).symm.trans hd
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr_rep x hd
  have hPs : IsSmooth (prodIrr x hd) := isSmooth_prodIrr x hd
  have hPf := GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd
  obtain ⟨h₁, h₂, h, Δ₁, Δ₂, Δ, hΔ₁, hΔ₂, hΔ, hI⟩ := GlobalTheory.T.ordered_forms_interleave_sum hA 𝔪 𝔫
  have w0 : Wd (x 0).rep (wtW Δ₁) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔪 (x 0).rep h0 h₁ Δ₁ hΔ₁
  have w1 : Wd (x 1).rep (wtW Δ₂) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔫 (x 1).rep h1 h₂ Δ₂ hΔ₂
  have wp : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Δ) :=
    GlobalTheory.T.word_occurs_product_interleave hA (x 0) (x 1) _ _ _ (GlobalTheory.T.ordered_word_letters_cuspidal Δ₁) (GlobalTheory.T.ordered_word_letters_cuspidal Δ₂) w0 w1 hI
  have wP : Wd (prodIrr x hd) (wtW Δ) := GlobalTheory.T.word_occurs_of_subquotient (prodIrr x hd) (prod₂ (x 0).rep (x 1).rep) hPs
    (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) _ wp
  have hτ := GlobalTheory.T.word_occurs_irreducible_subquotient hA (prodIrr x hd) hPs hPf (wtW Δ) wP
  obtain ⟨τ, hτP, hτW⟩ := hτ
  obtain ⟨𝔭, hτL⟩ := isL_of_exhaust hEx τ
  obtain ⟨h', z, hz, ⟨Γ, hΓ, hzL⟩, hcos⟩ := id hτL
  have s1 : InShW 𝔭 (wtW Δ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z hz Γ hzL (wtW Δ) (GlobalTheory.T.ordered_word_letters_cuspidal Δ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z hz) hcos.isSubquotient _ hτW)
    rwa [hΓ.1] at this
  have wΓ : Wd τ.ρ (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔭 τ.ρ hτL h' Γ hΓ
  have wΓP : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ hPs hτP _ wΓ
  have wΓ2 : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prod₂ _ _)
    (.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective) _ wΓP
  obtain ⟨h'', z', Δ', hz', hz'L, hmap, hsub⟩ := GlobalTheory.T.product_langlands_subquotient_segments hA 𝔪 𝔫 (x 0) (x 1) h0 h1
  have s2 : InShW (𝔪 + 𝔫) (wtW Γ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z' hz' Δ' hz'L (wtW Γ) (GlobalTheory.T.ordered_word_letters_cuspidal Γ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z' hz') hsub _ wΓ2)
    rwa [hmap] at this
  have he : 𝔪 + 𝔫 = 𝔭 := GlobalTheory.T.ordered_forms_mutual_shuffle_eq hA (𝔪 + 𝔫) 𝔭 h h' Δ Γ hΔ hΓ s1 s2
  obtain ⟨ψ⟩ := GlobalTheory.T.langlands_classification_order_free_equiv hFree (𝔪 + 𝔫) τ.ρ (IrrGL.rep ⟨_, c⟩) (he ▸ hτL) hy
  exact (IsSubquotient.of_surjective ψ.toIntertwiningMap ψ.toLinearEquiv.surjective).trans hτP

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k →
    (∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) →
    ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1),
      IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) :=
  fun hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy =>
    isSubquotient_prodIrr hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy

end GlobalTheory.CompanionTheory.LangSumSub

end
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_sum_subquotient_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k → (∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) → ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1), IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LangSumSub.main
end

section
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LanglandsMultiseg

theorem langlandsMultisegments_of_clauses (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    (hSoc : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSocleGL k)
    (hSeg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSegJacquet k)
    (hFree : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k)
    (hE : GlobalTheory.Published.LanglandsExhaustionGL) : GlobalTheory.Published.LanglandsMultisegments := by
  intro k _ _ _ _ _
  exact ⟨GlobalTheory.T.langlands_injective_of_socle hA (hSoc k) (hSeg k),
    fun 𝔪 𝔫 x y hd h₀ h₁ hy =>
      GlobalTheory.T.langlands_sum_subquotient_product hA (hSoc k) (hSeg k)
        (hFree k) (hE k) 𝔪 𝔫 x y hd h₀ h₁ hy⟩

end GlobalTheory.CompanionTheory.LanglandsMultiseg
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_multisegments_of_exhaustion_gl : (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSocleGL k) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSegJacquet k) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k) → GlobalTheory.Published.LanglandsExhaustionGL → GlobalTheory.Published.LanglandsMultisegments := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses
end
