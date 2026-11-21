import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPartnerCombinationGoodInertLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointInjectiveOnPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory

theorem exists_separating_extension_of_rel : ∀ {α β L : Type} [Infinite L] (S : Finset (α → L)) (r : β → α) (Rel : (α → L) → (β → L) → Prop), Function.Injective r → (∀ e ∈ S, ∀ e' ∈ S, ∀ f f', Rel e f → Rel e' f' → (e ∘ r = e' ∘ r ↔ f = f')) → ∃ tr : (α → L) → α → L, (∀ e ∈ S, ∀ f, Rel e f → ∀ k, f k = tr e (r k)) ∧ ∀ e ∈ S, ∀ e' ∈ S, (∃ k, e (r k) ≠ e' (r k)) → ∃ k, tr e (r k) ≠ tr e' (r k) := by
  intro α β L _ S r Rel hr H
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · exact ⟨id, fun _ _ _ _ k => isEmptyElim k, fun _ _ _ _ h => h⟩
  have hF : (⋃ e ∈ (S : Set (α → L)), {f | Rel e f}).Finite := by
    refine Set.Finite.biUnion S.finite_toSet fun e he => Set.Subsingleton.finite ?_
    intro f hf f' hf'
    exact (H e he e he f f' hf hf').1 rfl
  have hinf := hF.infinite_compl
  have hT : ((fun e : α → L => e ∘ r) '' (S : Set (α → L))).Countable :=
    (S.finite_toSet.image _).countable
  obtain ⟨n, hn⟩ := Set.countable_iff_exists_injOn.1 hT
  let j : (β → L) → (β → L) := fun c => (hinf.natEmbedding _ (n c)).1
  have hj : ∀ c, ∀ e ∈ S, ¬ Rel e (j c) := by
    intro c e he h
    exact (hinf.natEmbedding _ (n c)).2 (Set.mem_biUnion (Finset.mem_coe.2 he) h)
  have hji : ∀ e ∈ S, ∀ e' ∈ S, j (e ∘ r) = j (e' ∘ r) → e ∘ r = e' ∘ r := by
    intro e he e' he' h
    exact hn ⟨e, he, rfl⟩ ⟨e', he', rfl⟩ ((hinf.natEmbedding _).injective (Subtype.ext h))
  let g : (β → L) → (β → L) := fun c =>
    if h : ∃ f, ∃ e ∈ S, e ∘ r = c ∧ Rel e f then h.choose else j c
  have hg : ∀ c, (∃ e ∈ S, e ∘ r = c ∧ Rel e (g c)) ∨ g c = j c := by
    intro c
    by_cases h : ∃ f, ∃ e ∈ S, e ∘ r = c ∧ Rel e f
    · left
      have : g c = h.choose := dif_pos h
      rw [this]
      exact h.choose_spec
    · exact Or.inr (dif_neg h)
  refine ⟨fun e => Function.extend r (g (e ∘ r)) e, ?_, ?_⟩
  · intro e he f hf k
    have h : ∃ f, ∃ e' ∈ S, e' ∘ r = e ∘ r ∧ Rel e' f := ⟨f, e, he, rfl, hf⟩
    have h1 : g (e ∘ r) = h.choose := dif_pos h
    obtain ⟨e', he', h2, h3⟩ := h.choose_spec
    have h4 := (H e' he' e he _ _ h3 hf).1 h2
    show f k = Function.extend r (g (e ∘ r)) e (r k)
    rw [hr.extend_apply, h1, h4]
  · rintro e he e' he' ⟨k, hk⟩
    by_contra hc
    have hge : g (e ∘ r) = g (e' ∘ r) := by
      funext i
      by_contra hi
      refine hc ⟨i, ?_⟩
      show Function.extend r (g (e ∘ r)) e (r i) ≠ Function.extend r (g (e' ∘ r)) e' (r i)
      rwa [hr.extend_apply, hr.extend_apply]
    apply hk
    suffices h : e ∘ r = e' ∘ r from congrFun h k
    rcases hg (e ∘ r) with ⟨a, ha, h1, h2⟩ | h1 <;> rcases hg (e' ∘ r) with ⟨b, hb, h3, h4⟩ | h3
    · rw [← h1, ← h3]
      exact (H a ha b hb _ _ h2 h4).2 hge
    · exact absurd (by rw [← h3, ← hge]; exact h2) (hj (e' ∘ r) a ha)
    · exact absurd (by rw [← h1, hge]; exact h4) (hj (e ∘ r) b hb)
    · exact hji e he e' he' (by rw [← h1, ← h3, hge])

end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertValues_iff_inertLabels_carriedEigensystems : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ (i : Fin D.R.m) (p p' : A3.fam3.base3.Ix) c c', R.Carries p c → R.Carries p' c' → ((∀ k : A3.okI A3.A.μ0 × List ℕ, p.1.2 (k.1.1, k.2) = p'.1.2 (k.1.1, k.2)) ↔ (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D i) P d → c P d = c' P d)) := by
  first | exact @GlobalTheory.InertValLab.inert_vals_iff_labels | exact GlobalTheory.InertValLab.inert_vals_iff_labels | (intros; apply GlobalTheory.InertValLab.inert_vals_iff_labels <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertPlaces

theorem inert_places_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ (t : T) (P : Pl D.host.E), (∃ Q ∈ A3.okI t, R.plI Q = P) ↔ (Good R.toRealDat t P ∧ conjPl P = P) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h t P
  have hSb : (R.Sb : Set (Pl D.host.E)) = R.Pg := by rw [h.allPl]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨hfix, hoff⟩ := (h.inert.tie.okI t Q).1 hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hfix
    have hf : Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q := HeightOneSpectrum.ext hfix
    refine ⟨fun PP hPP => ⟨fun he => hoff ?_, fun hc => hoff ?_⟩, hf⟩
    · rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← he]; exact hm)
      · exact Or.inr (by rw [← he]; exact hm)
    · have e1 := GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc
      have e2 : PP = R.plI Q := by
        rw [← Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl PP, ← e1, hf]
      rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← e2]; exact hm)
      · exact Or.inr (by rw [← e2]; exact hm)
  · rintro ⟨hg, hf⟩
    have hnS : P ∉ (R.Sb : Set (Pl D.host.E)) := by
      rw [hSb]; intro hm; exact (hg P (Or.inl hm)).1 rfl
    have hio : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := by
      refine ⟨?_, hnS⟩
      rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hf]
    obtain ⟨Q, hQ⟩ := h.inert.onto P hio
    refine ⟨Q, (h.inert.tie.okI t Q).2 ⟨?_, ?_⟩, hQ⟩
    · rw [hQ]; exact hio.1
    · rw [hQ]
      rintro (hm | hm)
      · exact hnS hm
      · exact (hg P (Or.inr hm)).1 rfl

end GlobalTheory.InertPlaces
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ (t : T) (P : Pl D.host.E), (∃ Q ∈ A3.okI t, R.plI Q = P) ↔ (Good R.toRealDat t P ∧ conjPl P = P) := by
  atlas_forward_decl GlobalTheory.InertPlaces.inert_places_iff
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertEig

open Classical in

noncomputable def coeff (n : ℕ) (ok : List ℕ → Prop) (lab : ℕ → List ℕ → List ℤ) (b : List ℕ → ℂ) (d : List ℤ) : ℂ :=
  if h : ∃ s, ok s ∧ lab n s = d then b h.choose else 0

theorem coeff_cases {H : Type} [AddCommGroup H] [Module ℂ H] (n : ℕ) (ok : List ℕ → Prop) (lab : ℕ → List ℕ → List ℤ)
    (isLab : List ℤ → Prop) (hL : ∀ d, isLab d → ∃ s, ok s ∧ lab n s = d) (b : List ℕ → ℂ)
    (ops : List ℤ → Module.End ℂ H) (x : H) (hx : ∀ s, ok s → ops (lab n s) x = b s • x) (d : List ℤ) :
    (¬ isLab d ∧ coeff n ok lab b d = 0) ∨ ops d x = coeff n ok lab b d • x := by
  classical
  by_cases h : ∃ s, ok s ∧ lab n s = d
  · right
    have hf : coeff n ok lab b d = b h.choose := dif_pos h
    have h1 := hx _ h.choose_spec.1
    rw [h.choose_spec.2] at h1
    rw [hf]
    exact h1
  · left
    exact ⟨fun hl => h (hL d hl), dif_neg h⟩

theorem eig_of_single {H Γ ι W : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W]
    (e : H →ₗ[ℂ] (Γ → W)) (he : Function.Injective e) (rep : List ℤ → Finset ι) (act : Γ → ι → Γ)
    (ops : (List ℤ →₀ ℂ) → Module.End ℂ H)
    (hops : ∀ c x, e (ops c x) = fun g => c.sum fun d z => z • ∑ γ ∈ rep d, e x (act g γ))
    (f : List ℤ → ℂ) (x : H) (hx : ∀ d, (rep d = ∅ ∧ f d = 0) ∨ ops (Finsupp.single d 1) x = f d • x)
    (c : List ℤ →₀ ℂ) : ops c x = (c.sum fun d z => z * f d) • x := by
  have hd : ∀ d g, ∑ γ ∈ rep d, e x (act g γ) = f d • e x g := by
    intro d g
    rcases hx d with ⟨h0, hf⟩ | h1
    · rw [h0, hf, Finset.sum_empty, zero_smul]
    · have h2 := congrFun (hops (Finsupp.single d 1) x) g
      rw [h1, map_smul, Finsupp.sum_single_index (by simp), one_smul] at h2
      exact h2.symm
  apply he
  rw [hops c x, map_smul]
  funext g
  simp only [Pi.smul_apply, Finsupp.sum, hd, smul_smul, Finset.sum_smul]

theorem labIn_eq (n : ℕ) (s : List ℕ) : GlobalTheory.Hk3.labIn n s = labIn n s := rfl

set_option maxHeartbeats 1000000 in

theorem veig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (j : Fin D.R.m) (t : T) (hV : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H), GlobalTheory.Hk3.IsOpsV R j t hV → ∀ P, Good R t P → conjPl P = P → ∀ (b : List ℕ → ℂ) (y y' : (R.HV j t).H), (∀ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s → hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y = b s • y ∧ hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y' = b s • y') → ∀ cV : List ℤ →₀ ℂ, ∃ σ : ℂ, hV P cV y = σ • y ∧ hV P cV y' = σ • y' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hM j t hV hOps P hP hc b y y' hb cV
  have hL : ∀ d, IsLab (Vc D j) P d → ∃ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s ∧ labIn (Vc D j).rank s = d := by
    intro d hl
    obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) P d).1 hl
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := (GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank d).1 ⟨h1, h2, h3 hc⟩
    exact ⟨s, ⟨hs2, hs3, hs1⟩, (labIn_eq _ _).symm.trans hs4.symm⟩
  have hrep : ∀ d, ¬ IsLab (Vc D j) P d → GlobalTheory.Hk3.rep (Vc D j) P d = ∅ := by
    intro d hd
    classical
    exact dif_neg hd
  have key : ∀ x : (R.HV j t).H, (∀ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s →
      hV P (Finsupp.single (labIn (Vc D j).rank s) 1) x = b s • x) →
      hV P cV x = (cV.sum fun d z => z * coeff (Vc D j).rank (Formalism.L2.Col.InertTypeOk (Vc D j).rank) labIn b d) • x := by
    intro x hx
    refine eig_of_single (R.HV j t).e (hM.HV j t).1 (GlobalTheory.Hk3.rep (Vc D j) P) (fun g γ => g * (finHom (Vc D j)).rangeRestrict γ)
      (hV P) (fun c x => hOps P hP c x) _ x ?_ cV
    intro d
    rcases coeff_cases (Vc D j).rank (Formalism.L2.Col.InertTypeOk (Vc D j).rank) labIn (IsLab (Vc D j) P) hL b
      (fun d => hV P (Finsupp.single d 1)) x hx d with ⟨h0, hf⟩ | h1
    · exact Or.inl ⟨hrep d h0, hf⟩
    · exact Or.inr h1
  exact ⟨_, key y (fun s hs => (hb s hs).1), key y' (fun s hs => (hb s hs).2)⟩

end GlobalTheory.InertEig
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalOperators_common_eigenvalue_inertPrime : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (j : Fin D.R.m) (t : T) (hV : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H), GlobalTheory.Hk3.IsOpsV R j t hV → ∀ P, Good R t P → conjPl P = P → ∀ (b : List ℕ → ℂ) (y y' : (R.HV j t).H), (∀ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s → hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y = b s • y ∧ hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y' = b s • y') → ∀ cV : List ℤ →₀ ℂ, ∃ σ : ℂ, hV P cV y = σ • y ∧ hV P cV y' = σ • y' := by
  atlas_forward_decl GlobalTheory.InertEig.veig
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertTransferW

theorem complex_smul_left_cancel_of_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V] {a b : ℂ} {w : V} (hw : w ≠ 0) (h : a • w = b • w) :
    a = b := by
  by_contra hne
  apply hw
  have h2 : (a - b) • w = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

theorem field_smul_left_cancel_of_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {a b : K} {w : V} (hw : w ≠ 0)
    (h : a • w = b • w) : a = b := by
  by_contra hne
  apply hw
  have h2 : (a - b) • w = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

set_option maxHeartbeats 4000000 in

theorem inertEigenvalues_iff_thetaLift_inertLabels_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∀ (j : Fin D.R.m) c c' (u u' : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x x' : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) → (∀ i, (A3.liftI j A3.A.μ0).opAll i x' = u' i • x') → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ∈ R.Wc' j c' → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ≠ 0 → ((∀ k, u (Sum.inr k) = u' (Sum.inr k)) ↔ (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hW hE hS hTS hJunk j c c' u u' x x' hx hx' hc hc' hn hn'
  obtain ⟨hcore, hSF, -, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hE
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hW0, hWops, -, -, -, -, hWev, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hcore hS hX R.SF hSF j
  obtain ⟨hV, hVops, -⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models).2 j A3.A.μ0
  have K : ∀ {cc : Pl D.host.E → List ℤ → ℂ} {z : (A3.A.fam.L j A3.A.μ0).S.Forms},
      R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) ∈ R.Wc' j cc → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) ≠ 0 →
      ∀ P, Good R.toRealDat A3.A.μ0 P → ∀ cV cW, GlobalTheory.Hk3.MatchW R.toRealDat j A3.A.μ0 P cV cW → ∀ σ : ℂ,
      hV P cV (R.jV j A3.A.μ0 z) = σ • R.jV j A3.A.μ0 z → σ = GlobalTheory.Hk3.evC (Wc D j) P (cc P) cW := by
    intro cc z hz hz0 P hP cV cW hM σ hσ
    rw [hWc j cc] at hz
    have h1 := (GlobalTheory.T.theta_intertwines_matched_operators R.toRealDat F.lv2 hcore hS hX R.SF hSF j A3.A.μ0 P hP cV cW hM hV hVops).1 hW0 hWops
      (R.jV j A3.A.μ0 z)
    have h4 := hWev cc P hP cW _ hz
    have h5 : σ • R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) = GlobalTheory.Hk3.evC (Wc D j) P (cc P) cW • R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) :=
      ((R.thG j A3.A.μ0).map_smul σ (R.jV j A3.A.μ0 z)).symm.trans ((congrArg (R.thG j A3.A.μ0) hσ).symm.trans (h1.trans h4))
    exact complex_smul_left_cancel_of_ne_zero hz0 h5
  have hrank : (Vc D j).rank = (A3.A.fam.L j A3.A.μ0).n := R.B.rankL j
  have V1 : ∀ (Q : A3.okI A3.A.μ0) (sq : List ℕ), Formalism.L2.Col.InertTypeOk (Vc D j).rank sq → ∀ f,
      R.jV j A3.A.μ0 (A3.heckeLI j A3.A.μ0 (Q, sq) f) =
        hV (R.plI Q) (Finsupp.single (labIn (Vc D j).rank sq) 1) (R.jV j A3.A.μ0 f) := by
    intro Q sq hsq f
    have tie := (hW.inert.hL j A3.A.μ0).some
    refine ((GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models j A3.A.μ0 _
      (fun k : A3.okI A3.A.μ0 × List ℕ => R.plI k.1) (fun k => labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2) ?_ tie (Q, sq) hsq).2.2.2 hV hVops f)
    intro k hk
    obtain ⟨hg, hcj⟩ := (GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj R F hW A3.A.μ0 (R.plI k.1)).1 ⟨k.1, k.1.2, rfl⟩
    refine ⟨hg, hcj, ?_⟩
    exact ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank (labIn (Vc D j).rank k.2)).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1
  have hx0 : x ≠ 0 := by rintro rfl; exact hn (by simp)
  have hx0' : x' ≠ 0 := by rintro rfl; exact hn' (by simp)
  have hopx : ∀ k, A3.heckeLI j A3.A.μ0 k x = u (Sum.inr k) • x := fun k => hx (Sum.inr k)
  have hopx' : ∀ k, A3.heckeLI j A3.A.μ0 k x' = u' (Sum.inr k) • x' := fun k => hx' (Sum.inr k)
  constructor
  · intro hu P d hP hPc hd
    obtain ⟨Q, hQ, rfl⟩ := (GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj R F hW A3.A.μ0 P).2 ⟨hP, hPc⟩
    obtain ⟨cV, hM⟩ := ((hTS _ hP hPc).2 j).2 (Finsupp.single d 1)
    obtain ⟨σ, h1, h2⟩ := GlobalTheory.T.sphericalOperators_common_eigenvalue_inertPrime R.toRealDat hcore.models j A3.A.μ0 hV hVops _ hP hPc
      (fun sq => D.what₂.embLL (u (Sum.inr (⟨Q, hQ⟩, sq)))) (R.jV j A3.A.μ0 x) (R.jV j A3.A.μ0 x')
      (fun sq hsq => ⟨(V1 ⟨Q, hQ⟩ sq hsq x).symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx _)).trans (map_smulₛₗ _ _ _)),
        (V1 ⟨Q, hQ⟩ sq hsq x').symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx' _)).trans ((map_smulₛₗ _ _ _).trans
          (congrArg (fun a => D.what₂.embLL a • R.jV j A3.A.μ0 x') (hu _).symm)))⟩) cV
    have e1 := K hc hn _ hP cV _ hM σ h1
    have e2 := K hc' hn' _ hP cV _ hM σ h2
    unfold GlobalTheory.Hk3.evC at e1 e2
    rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul] at e1 e2
    exact e1.symm.trans e2
  · rintro hcc ⟨⟨Q0, hQ0⟩, sq⟩
    have hPl := (GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj R F hW A3.A.μ0 (R.plI Q0)).1 ⟨Q0, hQ0, rfl⟩
    rcases hJunk.2 j A3.A.μ0 (⟨Q0, hQ0⟩, sq) with h0 | ⟨y, hy, hop⟩
    · have a1 : u (Sum.inr (⟨Q0, hQ0⟩, sq)) • x = 0 :=
        (hopx (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun h0 x).trans (LinearMap.zero_apply x))
      have a2 : u' (Sum.inr (⟨Q0, hQ0⟩, sq)) • x' = 0 :=
        (hopx' (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun h0 x').trans (LinearMap.zero_apply x'))
      rw [(smul_eq_zero.mp a1).resolve_right hx0, (smul_eq_zero.mp a2).resolve_right hx0']
    · have a1 : u (Sum.inr (⟨Q0, hQ0⟩, sq)) = u (Sum.inr (⟨Q0, hQ0⟩, y)) := by
        exact field_smul_left_cancel_of_ne_zero hx0 ((hopx (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun hop x).trans (hopx (⟨Q0, hQ0⟩, y))))
      have a2 : u' (Sum.inr (⟨Q0, hQ0⟩, sq)) = u' (Sum.inr (⟨Q0, hQ0⟩, y)) := by
        exact field_smul_left_cancel_of_ne_zero hx0' ((hopx' (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun hop x').trans (hopx' (⟨Q0, hQ0⟩, y))))
      rw [a1, a2]
      rw [← hrank] at hy
      obtain ⟨cW, hM⟩ := ((hTS _ hPl.1 hPl.2).2 j).1 (Finsupp.single (labIn (Vc D j).rank y) 1)
      have b1 := K hc hn _ hPl.1 _ cW hM _ ((V1 ⟨Q0, hQ0⟩ y hy x).symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx _)).trans (map_smulₛₗ _ _ _)))
      have b2 := K hc' hn' _ hPl.1 _ cW hM _ ((V1 ⟨Q0, hQ0⟩ y hy x').symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx' _)).trans (map_smulₛₗ _ _ _)))
      apply D.what₂.embLL.injective
      refine b1.trans (Eq.trans ?_ b2.symm)
      unfold GlobalTheory.Hk3.evC
      refine Finsupp.sum_congr fun d _ => ?_
      split_ifs with hd
      · rw [hcc _ d hPl.1 hPl.2 hd]
      · rfl

end GlobalTheory.InertTransferW
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertEigenvalues_iff_thetaLift_inertLabels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∀ (j : Fin D.R.m) c c' (u u' : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x x' : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) → (∀ i, (A3.liftI j A3.A.μ0).opAll i x' = u' i • x') → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ∈ R.Wc' j c' → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ≠ 0 → ((∀ k, u (Sum.inr k) = u' (Sum.inr k)) ↔ (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) := by
  atlas_forward_decl GlobalTheory.InertTransferW.inertEigenvalues_iff_thetaLift_inertLabels_alt
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory

theorem exists_passage_of_labels {Ix C α β L : Type} [Infinite L] (S : Finset (α → L)) (r : β → α) (hr : Function.Injective r)
    (e : Ix → α → L) (hS : ∀ p, e p ∈ S) (Car : Ix → C → Prop) (Sys : C → (β → L) → Prop) (Lab : C → C → Prop)
    (hE : ∀ p p' c c', Car p c → Car p' c' → ((∀ k, e p (r k) = e p' (r k)) ↔ Lab c c'))
    (hW : ∀ c c' f f', Sys c f → Sys c' f' → ((∀ k, f k = f' k) ↔ Lab c c')) :
    ∃ t : (α → L) → α → L, (∀ p c, Car p c → ∀ f, Sys c f → ∀ k, f k = t (e p) (r k)) ∧
      ∀ a ∈ S, ∀ b ∈ S, (∃ k, a (r k) ≠ b (r k)) → ∃ k, t a (r k) ≠ t b (r k) := by
  obtain ⟨t, h1, h2⟩ := exists_separating_extension_of_rel S r
    (fun a f => ∃ p, e p = a ∧ ∃ c, Car p c ∧ Sys c f) hr (by
      rintro a - b - f f' ⟨p, rfl, c, hc, hf⟩ ⟨p', rfl, c', hc', hf'⟩
      constructor
      · intro h
        funext k
        exact (hW c c' f f' hf hf').2 ((hE p p' c c' hc hc').1 fun k => congrFun h k) k
      · intro h
        funext k
        exact (hE p p' c c' hc hc').2 ((hW c c' f f' hf hf').1 fun k => congrFun h k) k)
  exact ⟨t, fun p c hc f hf k => h1 (e p) (hS p) f ⟨p, rfl, c, hc, hf⟩ k, h2⟩

theorem exists_inert_passage_separating : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∃ tr, R.TrISem F tr ∧ ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) → ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hL hO hC hE hS hT hJ hI
  classical
  haveI : Infinite D.what₂.LL := Infinite.of_injective (Nat.cast : ℕ → D.what₂.LL) Nat.cast_injective
  have hr : Function.Injective (fun k : A3.okI A3.A.μ0 × List ℕ => ((k.1.1, k.2) : I0 × List ℕ)) := by
    rintro ⟨⟨a, ha⟩, b⟩ ⟨⟨a', ha'⟩, b'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  have key : ∀ j : Fin D.R.m, ∃ t : (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL,
      (∀ (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ), R.Carries p c → ∀ f : A3.okI A3.A.μ0 × List ℕ → D.what₂.LL,
        (∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0) →
        ∀ k, f k = t p.1.2 (k.1.1, k.2)) ∧
      ∀ a ∈ ((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd,
      ∀ b ∈ ((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd,
        (∃ k : A3.okI A3.A.μ0 × List ℕ, a (k.1.1, k.2) ≠ b (k.1.1, k.2)) →
        ∃ k : A3.okI A3.A.μ0 × List ℕ, t a (k.1.1, k.2) ≠ t b (k.1.1, k.2) := by
    intro j
    have hE' : ∀ (p p' : A3.fam3.base3.Ix) (c c' : Pl D.host.E → List ℤ → ℂ), R.Carries p c → R.Carries p' c' →
        ((∀ k : A3.okI A3.A.μ0 × List ℕ, p.1.2 (k.1.1, k.2) = p'.1.2 (k.1.1, k.2)) ↔
          (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) :=
      fun p p' c c' hc hc' => GlobalTheory.T.inertValues_iff_inertLabels_carriedEigensystems R F hL hO hC hE hS hT hJ hI j p p' c c' hc hc'
    have hW' : ∀ (c c' : Pl D.host.E → List ℤ → ℂ) (f f' : A3.okI A3.A.μ0 × List ℕ → D.what₂.LL),
        (∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0) →
        (∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f' k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c' ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0) →
        ((∀ k, f k = f' k) ↔
          (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) := by
      rintro c c' f f' ⟨u, x, hf, a1, a2, a3⟩ ⟨u', x', hf', b1, b2, b3⟩
      have V := GlobalTheory.T.inertEigenvalues_iff_thetaLift_inertLabels R F hL hO hC hE hS hT hJ j c c' u u' x x' a1 b1 a2 b2 a3 b3
      refine Iff.trans ?_ V
      exact forall_congr' fun k => by rw [hf k, hf' k]
    exact exists_passage_of_labels (Ix := A3.fam3.base3.Ix) (C := Pl D.host.E → List ℤ → ℂ) (L := D.what₂.LL)
      (((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd)
      (fun k : A3.okI A3.A.μ0 × List ℕ => ((k.1.1, k.2) : I0 × List ℕ)) hr (fun p => p.1.2)
      (fun p => Finset.mem_image.2 ⟨p.1, p.2, rfl⟩) (fun p c => R.Carries p c)
      (fun c f => ∃ (u : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ k, f k = u (Sum.inr k)) ∧
          (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) ∧
          R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0)
      (fun c c' => ∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d) hE' hW'
  choose tr h1 h2 using key
  refine ⟨tr, ?_, ?_⟩
  · rintro j p c hc u ⟨x, -, a1, a2, a3⟩ k
    exact h1 j p c hc (fun k => u (Sum.inr k)) ⟨u, x, fun _ => rfl, a1, a2, a3⟩ k
  · intro j p hp p' hp' h
    exact h2 j p.2 (Finset.mem_image.2 ⟨p, hp, rfl⟩) p'.2 (Finset.mem_image.2 ⟨p', hp', rfl⟩) h

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_inertPassage_carried_by_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∃ tr, R.TrISem F tr ∧ ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) → ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2) := by
  atlas_forward_decl GlobalTheory.exists_inert_passage_separating
end

section
noncomputable section

open NumberField Polynomial Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.FamSep

section General

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  {m : ℕ} (A : FamIn K G Pl0 T m)

theorem trScale_ne_zero_at {P : Pl0} (hq : A.q P ≠ 0) : trScale A.r m A.t A.q A.etaVal P ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))

theorem typesSep_of_local (hq : ∀ P : (A.fam.R A.fam.μ0).Pl, A.q ((A.fam.R A.fam.μ0).pl P) ≠ 0)
    (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep := by
  intro Sg hSg Sg' hSg' hne j
  obtain ⟨P, hP⟩ := (A.fam.R A.fam.μ0).sep_of_mem_ixFin hSg hSg' hne
  exact ⟨P, fun h => hP (dualPoly_inj (trScale_ne_zero_at A (hq P)) (A.const_of h0 Sg hSg _) (A.const_of h0 Sg' hSg' _) h)⟩

theorem typesSep_of_ok {s : ℕ} (hOk : A.fam.Ok s) (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep :=
  typesSep_of_local A (fun P => ((hOk.what₂ A.fam.μ0).q_pos P).ne') h0

end General

section Real

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Real

end GlobalTheory.FamSep

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.FamSep

theorem typesSep_of_ok_isFam : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {s : ℕ}, A.fam.Ok s → R.IsFam → A.fam.TypesSep :=
  fun {_ _ _ _ _ _ A _ _ _ _} _ _ hOk hF => typesSep_of_ok A hOk fun P => (hF.degR A.μ0 P).1

end GlobalTheory.FamSep
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Hk3

theorem typesSep3_of_pin : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ((∃ tr, R.TrISem F tr ∧ ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) → ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2)) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → A3.fam3.TypesSep3 := by
  intro hP hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hL hOk hCW hEx hJ hPin hPos hB
  have hSchur : SchurAll R.toRealDat := schurAll_of_cuspRapidDecay hP R.toRealDat
  have hTwo := GlobalTheory.T.exists_partner_combination_good_inert_lift hH R F hL hCW hEx hSchur
  have hAdj := GlobalTheory.AdjPart.adjoint_injective_on_part R hPos hB
  have hTr := GlobalTheory.T.exists_separating_inertPassage_carried_by_forms R F hL hOk hCW hEx hSchur hTwo hJ hAdj
  have hI := (hPin hTr).2
  exact A3.fam3.typesSep3_of (hOk.ok2.what₂ A3.fam3.F.μ0).comm
    (GlobalTheory.FamSep.typesSep_of_ok_isFam R.toRealDat hOk.ok2 hCW.base.fam) hI

end GlobalTheory.Hk3
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_types_separated_by_inert_places : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ((∃ tr, R.TrISem F tr ∧ ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) → ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2)) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → A3.fam3.TypesSep3 := by
  atlas_forward_decl GlobalTheory.Hk3.typesSep3_of_pin
end
