import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSemisimpleGaloisRepWeights
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisOfUnramifiedMatchStatement
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGalois
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingPadicAlgClPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedMuPartInBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.RepConjUniq

theorem main : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ' → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm := by
  intro D hAN i x ρ ρ' h1 h2
  obtain ⟨-, -, hCheb, hBN⟩ := hAN
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin : (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪ (D.nd.Q i : Set _)).Finite :=
    ((Formalism.MainNotions.SumRepresentations.placesOver_finite D.host.E (D.nd.l i) hl.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have hdense := hCheb _ hfin
  have hfrob : ∀ g ∈ {σ : G D.host.E D.nd.Om | ∃ w ∉ (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪
      (D.nd.Q i : Set _)), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ},
      ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly := by
    rintro σ ⟨w, hw, hsp, B, hB', hσ⟩
    simp only [Set.mem_union, not_or] at hw
    obtain ⟨⟨hwl, hwS⟩, hwQ⟩ := hw
    replace hwS : w ∉ D.nd.S i := by simpa using hwS
    replace hwQ : w ∉ D.nd.Q i := by simpa using hwQ
    have hso : SplitOut D.nd i w := ⟨hsp, hwl, hwS, hwQ⟩
    rw [h1.2.2 w hso B σ hB' hσ, h2.2.2 w hso B σ hB' hσ]
  have hall := GlobalTheory.BaseChangeConj.charpoly_eq_of_dense' ρ ρ' h1.1 h2.1 _ hdense hfrob
  exact hBN _ _ ρ ρ' h1.2.1 h2.2.1 hall

end GlobalTheory.RepConjUniq
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeGaloisRepQbar_conjugate_unique : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ' → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm := by
  atlas_forward_decl GlobalTheory.RepConjUniq.main
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) r) := by
  first | exact @GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois | exact GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois | (intros; apply GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

theorem point_determines : ∀ D : D7, SumRepresentations.adm1 D → SumRepresentations.adm5 D → (∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ) → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (P P' : D.naut.AV i), D.naut.ptV i P ≠ none → D.naut.ptV i P = D.naut.ptV i P' → (∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa') ∧ ∀ w, w ∉ D.nd.S i → w ∉ D.nd.Q i → (IsSplitPl D.host w → D.naut.locV i P w = D.naut.locV i P' w) ∧ (¬ IsSplitPl D.host w → ubc D.R.nV (D.naut.satV i P w) = ubc D.R.nV (D.naut.satV i P' w)) := by
  intro D h1 h5 hex hcomp i P P' hP hPP'
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hP
  obtain ⟨ρ, hρ⟩ := hex i x
  have hx' : D.naut.ptV i P' = some x := hPP' ▸ hx

  have key : ∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' →
      ∀ w, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w := by
    intro Pa Pa' hB hB' w
    have c := hcomp i x P Pa hx hB ρ hρ
    have c' := hcomp i x P' Pa' hx' hB' ρ hρ
    have e : D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) =
        D.naut.lpTw (isoLoc D.nd D.naut Pa' w) ((1 - (D.R.nV : ℝ)) / 2) := by
      by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
      · rw [← (c.2 w hw).2.1, ← (c'.2 w hw).2.1]
      · rw [← c.1 w hw, ← c'.1 w hw]
    have e2 := congrArg (fun a => D.naut.lpTw a (-((1 - (D.R.nV : ℝ)) / 2))) e
    simpa only [D.naut.lpTw_add, add_neg_cancel, D.naut.lpTw_zero] using e2
  refine ⟨fun Pa Pa' hB hB' => ?_, fun w _ _ => ?_⟩
  · exact h5.2.1 Pa Pa' hB.1 hB'.1 (Filter.Eventually.of_forall (key Pa Pa' hB hB'))
  · obtain ⟨Pa, hB⟩ := h1 i P
    obtain ⟨Pa', hB'⟩ := h1 i P'
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · rw [← hB.2.2.2.1 w hs, ← hB'.2.2.2.1 w hs, key Pa Pa' hB hB' w]
    · rw [← (hB.2.2.2.2.1 w hs).2, ← (hB'.2.2.2.2.1 w hs).2, key Pa Pa' hB hB' w]

end GlobalTheory.NRows
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_match_of_hecke_galois : ∀ D : D7, SumRepresentations.adm1 D → SumRepresentations.adm5 D → (∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ) → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (P P' : D.naut.AV i), D.naut.ptV i P ≠ none → D.naut.ptV i P = D.naut.ptV i P' → (∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa') ∧ ∀ w, w ∉ D.nd.S i → w ∉ D.nd.Q i → (IsSplitPl D.host w → D.naut.locV i P w = D.naut.locV i P' w) ∧ (¬ IsSplitPl D.host w → ubc D.R.nV (D.naut.satV i P w) = ubc D.R.nV (D.naut.satV i P' w)) := by
  atlas_forward_decl GlobalTheory.NRows.point_determines
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

open Pointwise

theorem ine_conj_of_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀,
      map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]
  have c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x := fun x => by
    show (g⁻¹ * g) x = x
    simp
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, m, c]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (m' _).1 (hσ.2 _ hx')
    rw [map_sub, c] at h
    exact h

theorem crys_unram_of_lgc : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), (∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) → (∀ w ∈ placesOver D.host.E (D.nd.l i),
      (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → ∀ x, D.naut.IsCrysW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
        ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) ∧
      ((D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) → ∀ x,
        (∀ P Pa, D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → D.naut.mono0 (isoLoc D.nd D.naut Pa w)) →
        D.naut.IsPotCrysW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)) ∧
    ∀ x w, w ∉ placesOver D.host.E (D.nd.l i) → w ∉ D.nd.S i → w ∉ D.nd.Q i → UnramAt (F := D.host.E) (r x) w := by
  intro D htie hadm hLGC i r hr
  obtain ⟨-, -, hGal⟩ := htie
  have hl : (D.nd.l i).Prime := Fact.out
  have key : ∀ x, ∃ P Pa, D.naut.ptV i P = some x ∧ IsBCV D.nd D.naut i P Pa := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hadm i P
    exact ⟨P, Pa, hP, hPa⟩
  have hunr : ∀ P Pa w, IsBCV D.nd D.naut i P Pa → w ∉ D.nd.Q i →
      (∀ k, w ∉ placesOver D.host.E (D.host.g k)) →
      w ∉ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) →
      D.naut.unr (isoLoc D.nd D.naut Pa w) := by
    intro P Pa w hB hQ hg hp
    by_cases hs : IsSplitPl D.host w
    · rw [hB.2.2.2.1 w hs]
      exact D.naut.locV_unr i P w hs hQ hg hp
    · exact (hB.2.2.2.2.1 w hs).1
  refine ⟨fun w hw => ⟨fun hl0 hl1 x => ?_, fun _ x hm => ?_⟩, fun x w hwl hwS hwQ => ?_⟩
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw
    refine ⟨(hGal.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩, fun τ hτ => h.2.2 τ hτ⟩
    rw [h.2.1, D.naut.unr_tw]
    refine hunr P Pa w hB (fun hq => D.nd.SQ_l i w (Or.inr hq) hw) (fun k => ?_) ?_
    · have hk : D.nd.l i ≠ D.host.g k := by
        fin_cases k
        · exact hl0
        · exact hl1
      exact SumRepresentations.not_over_of_ne hl (D.host.g_prime k) hk hw
    · split_ifs with hpd
      · exact SumRepresentations.not_over_of_ne hl D.host.pde'_prime (hpd ▸ D.host.pde_ne) hw
      · exact SumRepresentations.not_over_of_ne hl D.host.pde_prime hpd hw
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw
    refine (hGal.2.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩
    rw [h.2.1, D.naut.monomial_twist_iff]
    exact hm P Pa hP hB
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).1 w hwl
    have hS : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
        w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧
        w ∉ placesOver D.host.E (D.nd.l i)) := fun hh => hwS ((D.nd.S_def i w).2 hh)
    have hu : D.naut.unr (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) := by
      rw [h, D.naut.unr_tw]
      refine hunr P Pa w hB hwQ (fun k hk => hS ⟨?_, hwl⟩) (fun hk => hS ⟨Or.inr (Or.inr hk), hwl⟩)
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    have h1 := (D.naut.wdOf_unr i _ w hwl (hr x).1).1 hu
    intro A hA σ hσ
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 w) hA
    have hσ' : σ ∈ Ine (F := D.host.E) (g • D.nd.plOm.1 w) := by rw [hg]; exact hσ
    have h2 := h1 _ (ine_conj_of_smul hσ')
    have h3 : mapRep (iotaOQ D.nd D.naut i) (r x) σ = 1 := by
      have e : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      rw [e, map_mul, map_mul, h2, mul_one, ← map_mul, mul_inv_cancel, map_one]
    apply Units.ext
    have h4 := congrArg (fun u : GL (Fin D.R.nV) (Qbar (D.nd.l i)) => u.val) h3
    simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h4
    refine Matrix.map_injective (SumRepresentations.iotaOQ_injective D.nd D.naut i) ?_
    show (r x σ).val.map (iotaOQ D.nd D.naut i) = (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h4

end GlobalTheory.NRows
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_galois_local_weights : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), (∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) → SumRepresentations.At.G2 D.nd D.naut i r ∧ SumRepresentations.At.G4 D.nd i r := by
  first | exact @GlobalTheory.NRows.crys_unram_of_lgc | exact GlobalTheory.NRows.crys_unram_of_lgc | (intros; apply GlobalTheory.NRows.crys_unram_of_lgc <;> assumption)
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicAlgCl_embedding_and_place_norm_lt_one : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], ∃ (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E)), ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal := by
  first | exact @GlobalTheory.exists_embedding_padicAlgCl_place | exact GlobalTheory.exists_embedding_padicAlgCl_place | (intros; apply GlobalTheory.exists_embedding_padicAlgCl_place <;> assumption)
end

section
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem endSpanned_of_isIrrSub_of_isAlgClosed :
    ∀ {Γ E : Type} [Group Γ] [Field E] [IsAlgClosed E] {a : ℕ} (σ : Γ →* GL (Fin a) E)
      (U : Submodule E (Fin a → E)), IsIrrSub σ U → EndSpanned σ U := by
  intro Γ E _ _ _ a σ U h
  classical
  have hinv : ∀ g, ∀ v ∈ U, (Matrix.toLin' ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) v ∈ U :=
    fun g v hv => by rw [Matrix.toLin'_apply]; exact h.2.1 g v hv
  let r : Representation E Γ U :=
    { toFun := fun g => (Matrix.toLin' ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).restrict (hinv g)
      map_one' := by
        ext v i
        simp [LinearMap.restrict_apply]
      map_mul' := fun g g' => by
        ext v i
        simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec] }
  have hr : ∀ g (v : U), ((r g v : U) : Fin a → E) = ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).mulVec v :=
    fun g v => by simp [r, LinearMap.restrict_apply]
  have hirr : r.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation r) := by
      refine ⟨⊥, ⊤, fun hbt => h.1 ?_⟩
      have h2 := congrArg Subrepresentation.toSubmodule hbt
      change (⊥ : Submodule E U) = ⊤ at h2
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hv⟩ : U) ∈ (⊥ : Submodule E U) := by rw [h2]; trivial
      rw [Submodule.mem_bot] at this
      simpa using congrArg Subtype.val this
    refine ⟨fun W => ?_⟩
    have hle : W.toSubmodule.map U.subtype ≤ U := by
      rintro _ ⟨v, _, rfl⟩; exact v.2
    have hinvW : IsInv σ (W.toSubmodule.map U.subtype) := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨r g v, W.apply_mem_toSubmodule g hv, ?_⟩
      simp [hr]
    rcases h.2.2 _ hle hinvW with h1 | h1
    · left
      refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)
      have : (v : Fin a → E) ∈ W.toSubmodule.map U.subtype := ⟨v, hv, rfl⟩
      rw [h1, Submodule.mem_bot] at this
      show v ∈ (⊥ : Submodule E U)
      rw [Submodule.mem_bot]; exact Subtype.ext this
    · right
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      have : (v : Fin a → E) ∈ W.toSubmodule.map U.subtype := by rw [h1]; exact v.2
      obtain ⟨w, hw, hwv⟩ := this
      rwa [show w = v from Subtype.ext hwv] at hw
  have hs := GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed r hirr
  intro φ
  have hφ : φ ∈ Submodule.span E (Set.range r) := by rw [hs]; trivial
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨_, Submodule.subset_span ⟨g, rfl⟩, fun w => (hr g w).symm⟩
  | zero => exact ⟨0, Submodule.zero_mem _, fun w => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX, hXw⟩ := hx
    obtain ⟨Y, hY, hYw⟩ := hy
    exact ⟨X + Y, Submodule.add_mem _ hX hY, fun w => by rw [Matrix.add_mulVec, hXw, hYw]; simp⟩
  | smul c x _ hx =>
    obtain ⟨X, hX, hXw⟩ := hx
    exact ⟨c • X, Submodule.smul_mem _ c hX, fun w => by rw [Matrix.smul_mulVec, hXw]; simp⟩

end GlobalTheory.SplitField
end

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endSpanned_of_isIrrSub_of_isAlgClosed' : ∀ {Γ E : Type} [Group Γ] [Field E] [IsAlgClosed E] {a : ℕ} (σ : Γ →* GL (Fin a) E) (U : Submodule E (Fin a → E)), IsIrrSub σ U → EndSpanned σ U := by
  atlas_forward_decl GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed
end

section
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem endSpanned_of_endSpanned_map {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a : ℕ}
    (τ : Γ →* GL (Fin a) L) (U : Submodule L (Fin a → L))
    (h : EndSpanned (mapRep f τ) (Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L))))) :
    EndSpanned τ U := by
  classical
  intro φ
  set UE := Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L))) with hUE
  have hmap : ∀ (M : Matrix (Fin a) (Fin a) L) (v : Fin a → L),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v
    funext i
    exact (RingHom.map_mulVec f M v i).symm

  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype U)
  set Y : Matrix (Fin a) (Fin a) L := LinearMap.toMatrix' (U.subtype ∘ₗ φ ∘ₗ p) with hY
  have hYv : ∀ v : Fin a → L, Y.mulVec v = (φ (p v) : Fin a → L) := by
    intro v
    rw [hY, LinearMap.toMatrix'_mulVec]
    rfl
  have hYU : ∀ w : U, Y.mulVec (w : Fin a → L) = (φ w : Fin a → L) := by
    intro w
    rw [hYv]
    have : p (w : Fin a → L) = w := by
      have := LinearMap.congr_fun hp w
      simpa using this
    rw [this]
  have hYE : ∀ x ∈ UE, (Y.map f).mulVec x ∈ UE := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [hmap, hYv]
      exact Submodule.subset_span ⟨_, (φ (p v)).2, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact UE.add_mem hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact UE.smul_mem c hx
  let ψ : UE →ₗ[E] UE := (Matrix.mulVecLin (Y.map f)).restrict hYE
  obtain ⟨XE, hXE, hXEw⟩ := h ψ

  let d := Module.finrank L U
  let b := Module.finBasis L U
  let Φ : Matrix (Fin a) (Fin a) L →ₗ[L] (Fin a × Fin d → L) :=
    { toFun := fun M ik => (M.mulVec (b ik.2 : Fin a → L)) ik.1
      map_add' := by intro M N; funext ik; simp [Matrix.add_mulVec]
      map_smul' := by intro c M; funext ik; simp [Matrix.smul_mulVec] }
  let ΦE : Matrix (Fin a) (Fin a) E →ₗ[E] (Fin a × Fin d → E) :=
    { toFun := fun M ik => (M.mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1
      map_add' := by intro M N; funext ik; simp [Matrix.add_mulVec]
      map_smul' := by intro c M; funext ik; simp [Matrix.smul_mulVec] }
  set R := Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) with hR
  set RE := Set.range fun g => ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) with hRE
  have hrep : ∀ g, ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)
      = ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).map f := fun g => rfl
  have hΦE : ∀ M : Matrix (Fin a) (Fin a) L, ΦE (M.map f) = f ∘ Φ M := by
    intro M
    funext ik
    show ((M.map f).mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = f ((M.mulVec (b ik.2 : Fin a → L)) ik.1)
    rw [hmap]; rfl
  set t : Fin a × Fin d → L := fun ik => (φ (b ik.2) : Fin a → L) ik.1 with ht
  have hXt : ΦE XE = f ∘ t := by
    funext ik
    have hmem : f ∘ (b ik.2 : Fin a → L) ∈ UE := Submodule.subset_span ⟨_, (b ik.2).2, rfl⟩
    have := hXEw ⟨_, hmem⟩
    show (XE.mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = f ((φ (b ik.2) : Fin a → L) ik.1)
    rw [this]
    show ((Y.map f).mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = _
    rw [hmap, hYU]
    rfl
  have hEspan : f ∘ t ∈ Submodule.span E ((fun v => f ∘ v) '' (Φ '' R)) := by
    rw [← hXt]
    have h1 : ΦE XE ∈ Submodule.map ΦE (Submodule.span E RE) := Submodule.mem_map_of_mem hXE
    rw [Submodule.map_span] at h1
    convert h1 using 2
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, hΦE _⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, (hΦE _).symm⟩
  have hLspan := mem_span_of_map_mem_span f (Φ '' R) t hEspan
  rw [← Submodule.map_span] at hLspan
  obtain ⟨X, hX, hXt'⟩ := hLspan
  refine ⟨X, hX, fun w => ?_⟩
  have hb : ∀ k, X.mulVec (b k : Fin a → L) = (φ (b k) : Fin a → L) := by
    intro k
    funext i
    exact congrFun hXt' (i, k)
  have hext : (Matrix.mulVecLin X) ∘ₗ U.subtype = U.subtype ∘ₗ φ := b.ext fun k => by
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Submodule.subtype_apply]
    exact hb k
  exact LinearMap.congr_fun hext w

end GlobalTheory.SplitField
end

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endSpannedByRepMatrices_of_scalarExtension : ∀ {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a : ℕ} (τ : Γ →* GL (Fin a) L) (U : Submodule L (Fin a → L)), EndSpanned (mapRep f τ) (Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L)))) → EndSpanned τ U := by
  atlas_forward_decl GlobalTheory.SplitField.endSpanned_of_endSpanned_map
end

section
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem isoSub_summand_of_isInternal {Γ L : Type} [Group Γ] [Field L] {a n : ℕ}
    (τ : Γ →* GL (Fin a) L) (Us : Fin n → Submodule L (Fin a → L)) (hI : DirectSum.IsInternal Us)
    (hU : ∀ m, IsIrrSub τ (Us m)) (W : Submodule L (Fin a → L)) (hW : IsIrrSub τ W) :
    ∃ m, IsoSub τ W (Us m) := by
  classical
  let T : Γ → (Fin a → L) →ₗ[L] (Fin a → L) := fun g =>
    Matrix.mulVecLin ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)
  have hTv : ∀ g v, T g v = ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec v := fun g v => rfl
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap Us) hI
  let P : ∀ m, (Fin a → L) →ₗ[L] Us m := fun m =>
    (DirectSum.component L (Fin n) (fun k => Us k) m).comp
      (e.symm : (Fin a → L) →ₗ[L] DirectSum (Fin n) fun k => Us k)
  have hstab : ∀ g k, ∀ v ∈ Us k, T g v ∈ Us k := fun g k v hv => (hU k).2.1 g v hv
  let φ : Γ → ∀ k, Us k →ₗ[L] Us k := fun g k => (T g).restrict (hstab g k)
  have hcomm : ∀ g (d : DirectSum (Fin n) fun k => Us k),
      DirectSum.coeLinearMap Us (DFinsupp.mapRange.linearMap (φ g) d) = T g (DirectSum.coeLinearMap Us d) := by
    intro g
    have : (DirectSum.coeLinearMap Us).comp (DFinsupp.mapRange.linearMap (φ g)) =
        (T g).comp (DirectSum.coeLinearMap Us) := by
      apply DirectSum.linearMap_ext
      intro k
      apply LinearMap.ext; intro x
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, DFinsupp.mapRange.linearMap_apply]
      rw [show (DirectSum.of (fun i => Us i) k x) = DFinsupp.single k x from rfl]
      rw [show DFinsupp.mapRange.linearMap (φ g) (DFinsupp.single k x) = DFinsupp.single k (φ g k x) from
        DFinsupp.mapRange_single (hf := fun i => map_zero _)]
      rw [show (DFinsupp.single k ((φ g k) x) : DirectSum (Fin n) fun i => Us i) =
        DirectSum.of (fun i => Us i) k (φ g k x) from rfl]
      simp [DirectSum.coeLinearMap_of, φ]
      rw [show (DFinsupp.single k x : DirectSum (Fin n) fun i => Us i) = DirectSum.of (fun i => Us i) k x from rfl,
        DirectSum.coeLinearMap_of]
    intro d
    exact LinearMap.congr_fun this d
  have hequiv : ∀ g m v, (P m (T g v) : Fin a → L) = T g (P m v) := by
    intro g m v
    have h1 : e.symm (T g v) = DFinsupp.mapRange.linearMap (φ g) (e.symm v) := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      show _ = DirectSum.coeLinearMap Us _
      rw [hcomm]
      congr 1
      exact (e.apply_symm_apply v).symm
    simp only [P, LinearMap.comp_apply, LinearEquiv.coe_coe, h1]
    simp only [← DirectSum.apply_eq_component, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply]
    rfl
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).1 hW.1
  obtain ⟨m, hm⟩ : ∃ m, P m w ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw0
    have h0 : e.symm w = 0 := by
      ext k : 1
      have := h k
      simpa [P, ← DirectSum.apply_eq_component] using this
    have := e.apply_symm_apply w
    rw [h0, map_zero] at this
    exact this.symm
  refine ⟨m, ?_⟩
  have hKinv : IsInv τ (W ⊓ LinearMap.ker (P m)) := by
    rintro g v ⟨hvW, hvK⟩
    have hvK' : P m v = 0 := hvK
    refine ⟨hW.2.1 g v hvW, show P m _ = 0 from ?_⟩
    apply Subtype.ext
    rw [← hTv, hequiv, hvK']
    simp
  have hK : W ⊓ LinearMap.ker (P m) = ⊥ := by
    rcases hW.2.2 _ inf_le_left hKinv with h | h
    · exact h
    · exfalso
      have : w ∈ W ⊓ LinearMap.ker (P m) := by rw [h]; exact hwW
      exact hm this.2
  let R : Submodule L (Fin a → L) := (W.map (P m)).map (Us m).subtype
  have hRinv : IsInv τ R := by
    rintro g y ⟨y', ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨P m (T g v), ⟨T g v, hW.2.1 g v hv, rfl⟩, ?_⟩
    simp only [Submodule.coe_subtype]
    rw [hequiv, hTv]
  have hR : R = Us m := by
    rcases (hU m).2.2 R (Submodule.map_subtype_le _ _) hRinv with h | h
    · exfalso
      have : ((P m w : Us m) : Fin a → L) ∈ R := ⟨P m w, ⟨w, hwW, rfl⟩, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hm (Subtype.ext this)
    · exact h
  let f : W →ₗ[L] Us m := (P m).comp W.subtype
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have : (x : Fin a → L) ∈ W ⊓ LinearMap.ker (P m) := ⟨x.2, hx⟩
    rw [hK, Submodule.mem_bot] at this
    exact (Submodule.mem_bot L).2 (Subtype.ext this)
  have hsurj : Function.Surjective f := by
    intro u
    have hu : (u : Fin a → L) ∈ R := by rw [hR]; exact u.2
    obtain ⟨y, ⟨v, hv, rfl⟩, hy⟩ := hu
    exact ⟨⟨v, hv⟩, Subtype.ext hy⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun g v h => ?_⟩
  simp only [LinearEquiv.ofBijective_apply, f, LinearMap.comp_apply, Submodule.coe_subtype]
  have := hequiv g m (v : Fin a → L)
  rw [hTv, hTv] at this
  exact this

end GlobalTheory.SplitField
end

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Us : Fin n → Submodule L (Fin a → L)), DirectSum.IsInternal Us → (∀ m, IsIrrSub τ (Us m)) → ∀ W, IsIrrSub τ W → ∃ m, IsoSub τ W (Us m) := by
  atlas_forward_decl GlobalTheory.SplitField.isoSub_summand_of_isInternal
end

section
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

def coordMap {L E : Type} [Field L] [Field E] (f : L →+* E) (a : ℕ) :
    (Fin a → L) →ₛₗ[f] (Fin a → E) where
  toFun v := f ∘ v
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp [smul_eq_mul]

theorem coordMap_injective {L E : Type} [Field L] [Field E] (f : L →+* E) (a : ℕ) :
    Function.Injective (coordMap f a) := by
  intro v w h
  funext i
  exact f.injective (congrFun h i)

theorem descend_decomp {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a n : ℕ}
    (τ : Γ →* GL (Fin a) L) (Vs : Fin n → Submodule E (Fin a → E)) (hint : DirectSum.IsInternal Vs)
    (hinv : ∀ m, IsInv (mapRep f τ) (Vs m))
    (hspan : ∀ m, Vs m ≤ Submodule.span E ((fun v => f ∘ v) '' {v : Fin a → L | f ∘ v ∈ Vs m})) :
    ∃ Us : Fin n → Submodule L (Fin a → L), DirectSum.IsInternal Us ∧
      ∀ m, IsInv τ (Us m) ∧ Submodule.span E ((fun v => f ∘ v) '' (Us m : Set (Fin a → L))) = Vs m := by
  classical
  set F := coordMap f a with hF
  let Us : Fin n → Submodule L (Fin a → L) := fun m => (Vs m).comap F
  have hUs : ∀ m, (Us m : Set (Fin a → L)) = {v : Fin a → L | f ∘ v ∈ Vs m} := fun m => rfl
  obtain ⟨hindV, htopV⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Vs).1 hint
  refine ⟨Us, ?_, fun m => ⟨?_, ?_⟩⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · rw [iSupIndep_def]
      intro i
      rw [Submodule.disjoint_def]
      intro v hv1 hv2
      have hle : (⨆ (j : Fin n) (_ : j ≠ i), Us j) ≤ (⨆ (j : Fin n) (_ : j ≠ i), Vs j).comap F :=
        iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => Vs j) j hj)
      have h1 : F v ∈ Vs i := hv1
      have h2 : F v ∈ ⨆ (j : Fin n) (_ : j ≠ i), Vs j := hle hv2
      have h3 := (Submodule.disjoint_def.1 ((iSupIndep_def.1 hindV) i)) _ h1 h2
      exact coordMap_injective f a (by rw [h3, map_zero])
    · rw [eq_top_iff]
      intro v _
      have hle : (⨆ m, Vs m) ≤ Submodule.span E ((fun v => f ∘ v) '' ((⨆ m, Us m : Submodule L (Fin a → L)) : Set (Fin a → L))) := by
        refine iSup_le fun m => (hspan m).trans (Submodule.span_mono (Set.image_mono ?_))
        rw [← hUs m]
        exact le_iSup Us m
      have hv : f ∘ v ∈ ⨆ m, Vs m := by rw [htopV]; exact Submodule.mem_top
      have := mem_span_of_map_mem_span f _ v (hle hv)
      rwa [Submodule.span_eq] at this
  · intro g v hv
    have hv' : f ∘ v ∈ Vs m := hv
    show f ∘ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec v ∈ Vs m
    have hm : f ∘ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec v =
        ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).mulVec (f ∘ v) := by
      funext i
      exact RingHom.map_mulVec f _ v i
    rw [hm]
    exact hinv m g _ hv'
  · refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact hv
    · rw [hUs m]
      exact hspan m

end GlobalTheory.SplitField
end

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield : ∀ {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Vs : Fin n → Submodule E (Fin a → E)), DirectSum.IsInternal Vs → (∀ m, IsInv (mapRep f τ) (Vs m)) → (∀ m, Vs m ≤ Submodule.span E ((fun v => f ∘ v) '' {v : Fin a → L | f ∘ v ∈ Vs m})) → ∃ Us : Fin n → Submodule L (Fin a → L), DirectSum.IsInternal Us ∧ ∀ m, IsInv τ (Us m) ∧ Submodule.span E ((fun v => f ∘ v) '' (Us m : Set (Fin a → L))) = Vs m := by
  atlas_forward_decl GlobalTheory.SplitField.descend_decomp
end

section
section
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SplitField

theorem exists_finite_ext_absIrrSub : ∀ {K Γ ι : Type} [Field K] [Group Γ] [Finite ι] {a : ℕ} (ρ : ι → (Γ →* GL (Fin a) K)), (∀ j, IsSSRep (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j))) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), ∀ j W, IsIrrSub (mapRep (algebraMap K K') (ρ j)) W → AbsIrrSub (mapRep (algebraMap K K') (ρ j)) W := by
  intro K Γ ι _ _ _ a ρ hss
  classical
  have hdec := fun j => GlobalTheory.semisimple_matrix_rep_decomp (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j)) (hss j)
  choose n Vs hint hirr using hdec
  let b : ∀ j m, Module.Basis (Fin (Module.finrank (AlgebraicClosure K) (Vs j m))) (AlgebraicClosure K) (Vs j m) :=
    fun j m => Module.finBasis (AlgebraicClosure K) (Vs j m)
  let S : Set (AlgebraicClosure K) := Set.range (fun p : (Σ j, Σ m : Fin (n j), Fin (Module.finrank (AlgebraicClosure K) (Vs j m)) × Fin a) =>
    ((b p.1 p.2.1 p.2.2.1 : Vs p.1 p.2.1) : Fin a → AlgebraicClosure K) p.2.2.2)
  obtain ⟨K', _, _, _, f, hf, hS⟩ := exists_finite_field S (Set.finite_range _)
  refine ⟨K', inferInstance, inferInstance, inferInstance, ?_⟩
  intro j
  set τ := mapRep (algebraMap K K') (ρ j) with hτ
  have hcomp : mapRep f τ = mapRep (algebraMap K (AlgebraicClosure K)) (ρ j) := by
    rw [hτ, mapRep_mapRep]
    congr 1
    exact RingHom.ext hf
  have hsp : ∀ m, Vs j m ≤ Submodule.span (AlgebraicClosure K) ((fun v => f ∘ v) '' {v : Fin a → K' | f ∘ v ∈ Vs j m}) := by
    intro m
    have h1 : Vs j m = Submodule.span _ (Set.range fun k => ((b j m k : Vs j m) : Fin a → AlgebraicClosure K)) := by
      have := congrArg (Submodule.map (Vs j m).subtype) (b j m).span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
      refine this.symm.trans ?_
      rw [← Set.range_comp]; rfl
    conv_lhs => rw [h1]
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hc : ∀ i, ∃ c : K', f c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K) i :=
      fun i => hS ⟨⟨j, m, k, i⟩, rfl⟩
    choose c hc using hc
    have hfc : f ∘ c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K) := funext hc
    refine Submodule.subset_span ⟨c, ?_, ?_⟩
    · show f ∘ c ∈ Vs j m
      rw [hfc]; exact (b j m k).2
    · exact hfc
  obtain ⟨Us, hUi, hUs⟩ := GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield f τ (Vs j) (hint j) (fun m => hcomp ▸ (hirr j m).2.1) hsp
  have hES : ∀ m, EndSpanned τ (Us m) := by
    intro m
    apply GlobalTheory.T.endSpannedByRepMatrices_of_scalarExtension f τ (Us m)
    rw [(hUs m).2, hcomp]
    exact GlobalTheory.T.endSpanned_of_isIrrSub_of_isAlgClosed' _ _ (hirr j m)
  have hne : ∀ m, Us m ≠ ⊥ := by
    intro m h
    apply (hirr j m).1
    rw [← (hUs m).2, h]
    simp
  have hUirr : ∀ m, IsIrrSub τ (Us m) := fun m => isIrrSub_of_endSpanned τ (Us m) (hne m) (hUs m).1 (hES m)
  intro W hW
  obtain ⟨m, hm⟩ := GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal τ Us hUi hUirr W hW
  exact absIrrSub_of_endSpanned τ W hW.1 hW.2.1 (endSpanned_of_isoSub τ W (Us m) hW.2.1 hm (hES m))
end GlobalTheory.SplitField
end

open Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_ext_irrSub_absIrr : ∀ {K Γ ι : Type} [Field K] [Group Γ] [Finite ι] {a : ℕ} (ρ : ι → (Γ →* GL (Fin a) K)), (∀ j, IsSSRep (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j))) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), ∀ j W, IsIrrSub (mapRep (algebraMap K K') (ρ j)) W → AbsIrrSub (mapRep (algebraMap K K') (ρ j)) W := by
  atlas_forward_decl GlobalTheory.SplitField.exists_finite_ext_absIrrSub
end

section
section
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.DoubleBlock

open Matrix

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

theorem exists_emb (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : IsInv ρ W) :
    ∃ (σ : Γ →* GL (Fin (Module.finrank k W)) k) (φ : (Fin (Module.finrank k W) → k) ≃ₗ[k] W),
      ∀ g x, (φ ((σ g : Matrix _ _ k) *ᵥ x) : Fin a → k) = (ρ g : Matrix _ _ k) *ᵥ (φ x : Fin a → k) := by
  classical
  let φ : (Fin (Module.finrank k W) → k) ≃ₗ[k] W := (Module.finBasis k W).equivFun.symm
  let r : Γ → (W →ₗ[k] W) := fun g =>
    (Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k)).restrict (p := W) (q := W) (fun v hv => hW g v hv)
  have hr : ∀ g v, (r g v : Fin a → k) = (ρ g : Matrix _ _ k) *ᵥ (v : Fin a → k) := fun g v => rfl
  let m : Γ →* Matrix (Fin (Module.finrank k W)) (Fin (Module.finrank k W)) k :=
    { toFun := fun g => LinearMap.toMatrix' (φ.symm.toLinearMap ∘ₗ r g ∘ₗ φ.toLinearMap)
      map_one' := by
        rw [← LinearMap.toMatrix'_id]
        congr 1
        apply LinearMap.ext
        intro x
        have : r 1 (φ x) = φ x := by
          apply Subtype.ext
          rw [hr]; simp
        simp [this]
      map_mul' := fun g h => by
        rw [← LinearMap.toMatrix'_comp]
        congr 1
        apply LinearMap.ext
        intro x
        have : r (g * h) (φ x) = r g (r h (φ x)) := by
          apply Subtype.ext
          rw [hr, hr, hr]; simp
        simp [this] }
  refine ⟨m.toHomUnits, φ, fun g x => ?_⟩
  have : ((m.toHomUnits g : Matrix _ _ k)) *ᵥ x = φ.symm (r g (φ x)) := by
    change LinearMap.toMatrix' (φ.symm.toLinearMap ∘ₗ r g ∘ₗ φ.toLinearMap) *ᵥ x = _
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  rw [this, LinearEquiv.apply_symm_apply, hr]

theorem exists_emb_sum (ρ : Γ →* GL (Fin a) k) {d u : ℕ} (σ : Γ →* GL (Fin d) k)
    (τ : Γ →* GL (Fin u) k) (f₁ : (Fin d → k) →ₗ[k] (Fin a → k))
    (f₂ : (Fin u → k) →ₗ[k] (Fin a → k)) (i₁ : Function.Injective f₁) (i₂ : Function.Injective f₂)
    (h₁ : ∀ g x, f₁ ((σ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f₁ x)
    (h₂ : ∀ g x, f₂ ((τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f₂ x)
    (hd : Disjoint (LinearMap.range f₁) (LinearMap.range f₂)) :
    ∃ f : (Fin (d + u) → k) →ₗ[k] (Fin a → k), Function.Injective f ∧
      LinearMap.range f = LinearMap.range f₁ ⊔ LinearMap.range f₂ ∧
      ∀ g x, f ((SumRepresentations.At.sumRep σ τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f x := by
  let s : (Fin (d + u) → k) ≃ₗ[k] (Fin d → k) × (Fin u → k) :=
    (LinearEquiv.funCongrLeft k k finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ k k)
  have hs : ∀ x, s x = (fun i => x (finSumFinEquiv (Sum.inl i)), fun i => x (finSumFinEquiv (Sum.inr i))) :=
    fun x => rfl
  refine ⟨(f₁.coprod f₂) ∘ₗ s.toLinearMap, ?_, ?_, fun g x => ?_⟩
  · have : Function.Injective (f₁.coprod f₂) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
        LinearMap.ker_eq_bot.2 i₁, LinearMap.ker_eq_bot.2 i₂, Submodule.prod_bot]
    exact this.comp s.injective
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, LinearMap.range_coprod]
  · have key : s ((SumRepresentations.At.sumRep σ τ g : Matrix _ _ k) *ᵥ x) =
        ((σ g : Matrix _ _ k) *ᵥ (s x).1, (τ g : Matrix _ _ k) *ᵥ (s x).2) := by
      have hM : (SumRepresentations.At.sumRep σ τ g).val = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (σ g).val 0 0 (τ g).val) := rfl
      rw [hM, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, hs, hs]
      ext i <;> simp [Function.comp_def]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key, LinearMap.coprod_apply, h₁, h₂,
      Matrix.mulVec_add]

theorem exists_conj (ρ : Γ →* GL (Fin a) k) {n : ℕ} (τ : Γ →* GL (Fin n) k)
    (f : (Fin n → k) →ₗ[k] (Fin a → k)) (hi : Function.Injective f) (hs : LinearMap.range f = ⊤)
    (h : ∀ g x, f ((τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f x) :
    ∃ (hn : n = a) (Pm : GL (Fin a) k), ∀ g,
      ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
        Matrix.reindex (finCongr hn) (finCongr hn) ((τ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  classical
  let e := LinearEquiv.ofBijective f ⟨hi, LinearMap.range_eq_top.1 hs⟩
  have hn : n = a := by simpa using e.finrank_eq
  subst hn
  let Pm : GL (Fin n) k := ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hP : ∀ x, (Pm : Matrix _ _ k) *ᵥ x = f x := fun x => LinearMap.toMatrix'_mulVec _ _
  refine ⟨rfl, Pm, fun g => ?_⟩
  have : ρ g * Pm = Pm * τ g := by
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Units.val_mul, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hP, h]
  rw [mul_assoc, this, inv_mul_cancel_left]
  simp

theorem exists_conj_double : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsSSRep ρ → IsInv ρ W₁ → IsInv ρ W₂ → W₁ ≠ ⊥ → W₁ ⊓ W₂ = ⊥ → IsoSub ρ W₁ W₂ → ∃ (d u : ℕ) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (h : d + d + u = a) (Pm : GL (Fin a) k), 0 < d ∧ ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k) := by
  intro k Γ _ _ a ρ W₁ W₂ hss h₁ h₂ hne hdis ⟨e, he⟩
  have h12 : IsInv ρ (W₁ ⊔ W₂) := by
    intro g v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem_sup (h₁ g x hx) (h₂ g y hy)
  obtain ⟨U, hU, hc⟩ := hss _ h12
  obtain ⟨σ, φ, hφ⟩ := exists_emb ρ W₁ h₁
  obtain ⟨υ, ψ, hψ⟩ := exists_emb ρ U hU
  have r₁ : LinearMap.range (W₁.subtype ∘ₗ φ.toLinearMap) = W₁ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have r₂ : LinearMap.range (W₂.subtype ∘ₗ (φ.trans e).toLinearMap) = W₂ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have r₃ : LinearMap.range (U.subtype ∘ₗ ψ.toLinearMap) = U := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨f, fi, fr, hf⟩ := exists_emb_sum ρ σ σ (W₁.subtype ∘ₗ φ.toLinearMap)
    (W₂.subtype ∘ₗ (φ.trans e).toLinearMap) (W₁.injective_subtype.comp φ.injective)
    (W₂.injective_subtype.comp (φ.trans e).injective) (fun g x => hφ g x)
    (fun g x => by
      have := he g (φ x) (h₁ g _ (φ x).2)
      have h' : φ ((σ g : Matrix _ _ k) *ᵥ x) = ⟨_, h₁ g _ (φ x).2⟩ := Subtype.ext (hφ g x)
      change (e (φ ((σ g : Matrix _ _ k) *ᵥ x)) : Fin a → k) = _
      rw [h', this]
      rfl)
    (by rw [r₁, r₂]; exact disjoint_iff.2 hdis)
  rw [r₁, r₂] at fr
  obtain ⟨F, Fi, Fr, hF⟩ := exists_emb_sum ρ (SumRepresentations.At.sumRep σ σ) υ f (U.subtype ∘ₗ ψ.toLinearMap) fi
    (U.injective_subtype.comp ψ.injective) hf (fun g x => hψ g x)
    (by rw [fr, r₃]; exact hc.disjoint)
  rw [fr, r₃, hc.sup_eq_top] at Fr
  obtain ⟨hn, Pm, hP⟩ := exists_conj ρ _ F Fi Fr hF
  exact ⟨_, _, σ, υ, hn, Pm, Nat.pos_of_ne_zero (fun h0 => hne (Submodule.finrank_eq_zero.1 h0)), hP⟩

end GlobalTheory.DoubleBlock
end

open Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_double_block_of_iso_subspaces : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsSSRep ρ → IsInv ρ W₁ → IsInv ρ W₂ → W₁ ≠ ⊥ → W₁ ⊓ W₂ = ⊥ → IsoSub ρ W₁ W₂ → ∃ (d u : ℕ) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (h : d + d + u = a) (Pm : GL (Fin a) k), 0 < d ∧ ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k) := by
  atlas_forward_decl GlobalTheory.DoubleBlock.exists_conj_double
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AbsIrrConstituents

theorem mapRep_comp {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {a : ℕ}
    (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) :
    mapRep (g.comp f) ρ = mapRep g (mapRep f ρ) := by
  ext x i j
  rfl

theorem fixedJumps_nodup (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (τ : D.host.E →+* Qbar (D.nd.l i)) :
    (D.naut.locAutHodgeTateWeightsLevelZero i τ).Nodup := by
  have h1 := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ
  rw [D.nbc.embAV_inf i P] at h1
  have h2 := (D.nbc.infW_alg _ (D.nbc.wtAU _ (D.nbc.embAV i P)) ((D.naut.iotaQC i).toRingHom.comp τ)).1
  have h3 := h2.map (f := fun z : ℂ => -z + ((D.R.nV : ℂ) - 1) / 2) (fun a b hab => by simpa using hab)
  rw [← h1] at h3
  exact h3.of_map _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem mem_of_induces' (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  apply (h _).mp
  have e : τ (((l : ℕ) : 𝓞 E) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    simp only [map_natCast]
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem sumRep_coe {k Γ : Type} [CommRing k] [Group Γ] {a b : ℕ} (ρ : Γ →* GL (Fin a) k)
    (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix _ _ k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

theorem coe_mapRep {k L Γ : Type} [CommRing k] [CommRing L] [Group Γ] {a : ℕ} (f : k →+* L)
    (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) = (ρ g : Matrix (Fin a) (Fin a) k).map f := rfl

theorem mapRep_sumRep {k L Γ : Type} [CommRing k] [CommRing L] [Group Γ] {a b : ℕ} (f : k →+* L)
    (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) :
    mapRep f (SumRepresentations.At.sumRep ρ ρ') = SumRepresentations.At.sumRep (mapRep f ρ) (mapRep f ρ') := by
  ext g i j
  rw [coe_mapRep, sumRep_coe, sumRep_coe, coe_mapRep, coe_mapRep]
  simp only [Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem contQ_sumRep (D : D7) (i : D.nd.Loc) {a b : ℕ}
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)))
    (ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i)))
    (h : SumRepresentations.At.ContQ D.nd i ρ) (h' : SumRepresentations.At.ContQ D.nd i ρ') : SumRepresentations.At.ContQ D.nd i (SumRepresentations.At.sumRep ρ ρ') := by
  unfold SumRepresentations.At.ContQ at *
  simp only [sumRep_coe, Matrix.reindex_apply]
  exact (Continuous.matrix_fromBlocks h continuous_const continuous_const h').matrix_submatrix _ _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem rel_map' {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {a d u : ℕ} (h : d + d + u = a)
    (ρ : Γ →* GL (Fin a) k) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (Pm : GL (Fin a) k)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
        Matrix.reindex (finCongr h) (finCongr h)
          ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix _ _ k)) :
    ∀ g, (((Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) k →+* Matrix (Fin a) (Fin a) L).toMonoidHom Pm)⁻¹ *
        mapRep f ρ g * Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) k →+* Matrix (Fin a) (Fin a) L).toMonoidHom Pm :
          GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      Matrix.reindex (finCongr h) (finCongr h)
        ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep (mapRep f σ) (mapRep f σ)) (mapRep f υ) g : GL (Fin (d + d + u)) L) :
          Matrix _ _ L) := by
  subst h
  intro g
  have e1 : (Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm)⁻¹ *
      mapRep f ρ g * Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm =
      Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* Matrix _ _ L).toMonoidHom
        (Pm⁻¹ * ρ g * Pm) := by
    simp only [map_mul, map_inv]; rfl
  rw [e1]
  show ((Pm⁻¹ * ρ g * Pm : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k).map f = _
  rw [hrel g]
  simp only [finCongr_refl, Matrix.reindex_refl_refl]
  rw [← mapRep_sumRep, ← mapRep_sumRep, coe_mapRep]

theorem jumps_not_nodup' (D : D7) (ht : SumRepresentations.tie0 D) (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hτ : InducesW D.nd i τ w)
    (hpl : ∀ w', InducesW D.nd i τ w' → w' ∈ placesOver D.host.E (D.nd.l i))
    {a d u : ℕ} (h : d + d + u = a) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)))
    (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin d) (Qbar (D.nd.l i)))
    (υ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin u) (Qbar (D.nd.l i))) (Pm : GL (Fin a) (Qbar (D.nd.l i)))
    (hd : 0 < d) (hc : SumRepresentations.At.ContQ D.nd i ρ) (hcσ : SumRepresentations.At.ContQ D.nd i σ) (hcυ : SumRepresentations.At.ContQ D.nd i υ)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) (Qbar (D.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) =
        Matrix.reindex (finCongr h) (finCongr h)
          ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) (Qbar (D.nd.l i))) :
            Matrix _ _ (Qbar (D.nd.l i))))
    (hdR : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i ρ w') :
    ¬ (D.naut.jumpsW i ρ τ).Nodup := by
  intro hnd
  subst h
  obtain ⟨-, -, hJC, hG⟩ := ht.2.2
  obtain ⟨-, hconj, hsum, -⟩ := hG i
  have hPm : ∀ g, SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g = Pm⁻¹ * ρ g * Pm := by
    intro g; ext1; rw [hrel g]; simp only [finCongr_refl, Matrix.reindex_refl_refl]
  have hcA := contQ_sumRep D i σ σ hcσ hcσ
  obtain ⟨hdRc, -, hJc⟩ := hconj _ ρ _ hc Pm hPm
  obtain ⟨hdRs, -, hJs⟩ := hsum _ _ _ υ hcA hcυ
  obtain ⟨hdRσ, -, hJσ⟩ := hsum _ _ σ σ hcσ hcσ
  have hdR' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ) w' :=
    fun w' hw' => (hdRc w' (hpl w' hw')).2 (hdR w' hw')
  have hdRA : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep σ σ) w' ∧ D.naut.IsdRW i υ w' :=
    fun w' hw' => (hdRs w' (hpl w' hw')).1 (hdR' w' hw')
  have hdRσ' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i σ w' ∧ D.naut.IsdRW i σ w' :=
    fun w' hw' => (hdRσ w' (hpl w' hw')).1 (hdRA w' hw').1
  have e : D.naut.jumpsW i ρ τ = D.naut.jumpsW i σ τ + D.naut.jumpsW i σ τ + D.naut.jumpsW i υ τ := by
    rw [← hJc τ hdR, hJs τ hdRA, hJσ τ hdRσ']
  have hcard := hJC i _ σ w τ hw hτ (hdRσ' w hτ).1
  rw [e] at hnd
  have h2 := (Multiset.nodup_add.1 (Multiset.nodup_add.1 hnd).1).2.2
  obtain ⟨j, hj⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard ▸ hd)
  exact Multiset.disjoint_left.1 h2 hj hj

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem continuous_blocks' {k Γ : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [Group Γ]
    [TopologicalSpace Γ] {a b c : ℕ} (ρ : Γ →* GL (Fin a) k) (ρ₁ : Γ →* GL (Fin b) k)
    (ρ₂ : Γ →* GL (Fin c) k) (h : b + c = a) (Pm : GL (Fin a) k)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) :
    (Continuous fun g => ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) ∧
      Continuous fun g => ((ρ₂ g : GL (Fin c) k) : Matrix (Fin c) (Fin c) k) := by
  subst h
  have hM : Continuous fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k) := by
    have e : (fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)) = fun g =>
        ((Pm⁻¹ : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k) * (ρ g : Matrix _ _ k) * (Pm : Matrix _ _ k) := by
      funext g
      rw [← Units.val_mul, ← Units.val_mul, hrel g]
      simp only [finCongr_refl, Matrix.reindex_refl_refl]
    rw [e]
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  constructor
  · have e : (fun g => ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) = fun g =>
        (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix
          (finSumFinEquiv ∘ Sum.inl) (finSumFinEquiv ∘ Sum.inl) := by
      funext g; ext i j; simp [sumRep_coe]
    rw [e]; exact hM.matrix_submatrix _ _
  · have e : (fun g => ((ρ₂ g : GL (Fin c) k) : Matrix (Fin c) (Fin c) k)) = fun g =>
        (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix
          (finSumFinEquiv ∘ Sum.inr) (finSumFinEquiv ∘ Sum.inr) := by
      funext g; ext i j; simp [sumRep_coe]
    rw [e]; exact hM.matrix_submatrix _ _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem absIrr_and_distinct_constituents : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), (∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) → SumRepresentations.At.G3a D.nd i r := by
  intro D ht hadm hH i r hr
  classical
  letI alg : Algebra (Kf D.nd i) (Qbar (D.nd.l i)) := (D.naut.iotaQ i).toAlgebra
  have hss : ∀ x, IsSSRep (mapRep (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i)))
      (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x))) := by
    intro x
    let f : AlgebraicClosure (Kf D.nd i) →ₐ[Kf D.nd i] Qbar (D.nd.l i) := IsAlgClosed.lift
    letI : Algebra (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i)) := f.toRingHom.toAlgebra
    apply SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))
    have e : ((algebraMap (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i))).comp
        (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i)))).comp (algebraMap (D.nd.O i) (Kf D.nd i)) =
        iotaOQ D.nd D.naut i := by
      ext z
      show f (algebraMap (Kf D.nd i) _ (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)
      rw [f.commutes]; rfl
    rw [← mapRep_comp, ← mapRep_comp, e]
    exact (hr x).2.1
  obtain ⟨K', hF, hA, hFD, hsplit⟩ :=
    GlobalTheory.T.exists_finiteDimensional_ext_irrSub_absIrr (fun x => mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) hss
  refine ⟨K', hF, hA, hFD, fun x => ⟨?_, ?_⟩⟩
  · rw [mapRep_comp]; exact hsplit x
  · intro W₁ W₂ h1 h2 hdis hiso
    let f' : K' →ₐ[Kf D.nd i] Qbar (D.nd.l i) := IsAlgClosed.lift
    have e' : (f'.toRingHom).comp ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) =
        iotaOQ D.nd D.naut i := by
      ext z
      show f' (algebraMap (Kf D.nd i) K' (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)
      rw [f'.commutes]; rfl
    have hQ : mapRep f'.toRingHom (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) =
        mapRep (iotaOQ D.nd D.naut i) (r x) := by
      rw [← mapRep_comp, e']
    have hssK : IsSSRep (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) := by
      letI : Algebra K' (Qbar (D.nd.l i)) := f'.toRingHom.toAlgebra
      apply SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))
      show IsSSRep (mapRep f'.toRingHom _)
      rw [hQ]; exact (hr x).2.1
    obtain ⟨d, u, σ, υ, h, Pm, hd, hrel⟩ := GlobalTheory.T.exists_conj_double_block_of_iso_subspaces _ W₁ W₂ hssK h1.2.1 h2.2.1 h1.1 hdis hiso
    have hrelQ := rel_map' f'.toRingHom h _ σ υ Pm hrel
    rw [hQ] at hrelQ
    have hcQ : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x)) := (hr x).1
    obtain ⟨hcA, hcυ⟩ := continuous_blocks' _ _ _ h _ hrelQ hcQ
    have hcσ : SumRepresentations.At.ContQ D.nd i (mapRep f'.toRingHom σ) :=
      (continuous_blocks' (SumRepresentations.At.sumRep (mapRep f'.toRingHom σ) (mapRep f'.toRingHom σ))
        (mapRep f'.toRingHom σ) (mapRep f'.toRingHom σ) rfl 1 (fun g => by simp) hcA).1
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hadm i P
    obtain ⟨-, hon⟩ := hH i x P Pa hP hPa _ (hr x)
    obtain ⟨τ, w, hτw⟩ := GlobalTheory.T.exists_padicAlgCl_embedding_and_place_norm_lt_one D.host.E (D.nd.l i)
    have hpl : ∀ w', InducesW D.nd i τ w' → w' ∈ placesOver D.host.E (D.nd.l i) :=
      fun w' hw' => mem_of_induces' D.host.E (D.nd.l i) τ w' hw'
    have hτ : InducesW D.nd i τ w := hτw
    have hJ := (hon w (hpl w hτ)).2.2 τ hτ
    refine jumps_not_nodup' D ht i τ w (hpl w hτ) hτ hpl h _ _ _ _ hd hcQ hcσ hcυ hrelQ
      (fun w' hw' => (hon w' (hpl w' hw')).1) ?_
    rw [hJ]; exact fixedJumps_nodup D i P τ

end GlobalTheory.AbsIrrConstituents
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_galois_local_weights_de_rham : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), (∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) → SumRepresentations.At.G3a D.nd i r := by
  first | exact @GlobalTheory.AbsIrrConstituents.absIrr_and_distinct_constituents | exact GlobalTheory.AbsIrrConstituents.absIrr_and_distinct_constituents | (intros; apply GlobalTheory.AbsIrrConstituents.absIrr_and_distinct_constituents <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_param_of_thetaLift_baseChange : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm3 D → SumRepresentations.ArchimedeanSignatureMatching D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), thetaOf D.nd D.naut i σ P → IsBCV D.nd D.naut i P Pa → (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa → ∃ Sig, HasParamW D.nd D.naut i σ Sig ∧ IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  first | exact @GlobalTheory.RowThetaParam.param_of_theta | exact GlobalTheory.RowThetaParam.param_of_theta | (intros; apply GlobalTheory.RowThetaParam.param_of_theta <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows.Parts

theorem lgc : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
  intro D t0 a2 a5 i x P Pa hP hPa ρ hρ
  obtain ⟨ρ0, hc, hs, hw, hl⟩ := GlobalTheory.T.exists_semisimple_galois_rep_weights D t0 a2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := GlobalTheory.T.heckeGaloisRepQbar_conjugate_unique D a5 i x ρ0 ρ (GlobalTheory.T.hecke_galois_of_unramified_match D i x P Pa hP hPa ρ0 hc hs hw) hρ
  obtain ⟨c1, c2, c3⟩ := (t0.2.2.2.2.2 i).2.1 _ ρ0 ρ hc Pm hPm
  refine ⟨fun w h => (c2 w (Or.inl h)).trans (hw w h), fun w h => ⟨(c1 w h).2 (hl w h).1, (c2 w (Or.inr (hl w h).1)).trans (hl w h).2.1, fun τ hτ => ?_⟩⟩
  rw [c3 τ, (hl w h).2.2 τ hτ]
  intro w' hw'
  obtain rfl : w' = w := HeightOneSpectrum.ext (Ideal.ext fun y => (hw' y).symm.trans (hτ y))
  exact (hl _ h).1

theorem h41 (D : D7) (a : SumRepresentations.AdmAt D) : SumRepresentations.ReducedFamilyProposition D := by
  obtain ⟨⟨t0, hO, a1, a2, a3, a4, a5⟩, a7⟩ := a
  have ex : ∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := fun i x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := a1 i P
    obtain ⟨ρ, hc, hs, hw, -⟩ := GlobalTheory.T.exists_semisimple_galois_rep_weights D t0 a2 i P Pa hPa
    exact ⟨ρ, GlobalTheory.T.hecke_galois_of_unramified_match D i x P Pa hP hPa ρ hc hs hw⟩
  have lg := lgc D t0 a2 a5
  intro i
  refine ⟨⟨fun x => (ex i x).choose, fun x => (ex i x).choose_spec⟩, GlobalTheory.T.unramified_match_of_hecke_galois D a1 a5 ex lg i, fun r hr => ?_⟩
  have he := fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hr x)
  exact ⟨(GlobalTheory.T.hecke_galois_local_weights D t0 a1 lg i r he).1, GlobalTheory.T.hecke_galois_local_weights_de_rham D t0 a1 lg i r he, (GlobalTheory.T.hecke_galois_local_weights D t0 a1 lg i r he).2⟩

theorem h42 (D : D7) (a : SumRepresentations.AdmAt D) (s : GlobalTheory.RowCopy.RowSize D) (hk : GlobalTheory.RowCopy.HeckeSplitOne D)
    (l : ∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) (th : GlobalTheory.RowCopy.ThetaOne D) : SumRepresentations.ReducedParameterProposition D := by
  obtain ⟨⟨t0, hO, a1, a2, a3, a4, a5⟩, a7⟩ := a
  intro i σ hσ
  obtain ⟨P, hP⟩ := th i σ hσ
  obtain ⟨Pa, hPa⟩ := a1 i P
  obtain ⟨Sig, h1, h2⟩ := GlobalTheory.T.row_param_of_thetaLift_baseChange D t0 a3 a4 a5 i σ P Pa hP hPa (GlobalTheory.T.twisted_mu_part_in_base_change D t0 a3 a5 a7 s hk i σ P Pa hσ hP hPa)
  refine ⟨⟨⟨_, (l i σ).2 hσ, (l i σ).1⟩, P, hP⟩, Sig, h1, fun P' hP' => ?_⟩
  obtain rfl : P = P' := by
    by_contra hne
    exact hP.1 (le_bot_iff.1 ((le_inf hP.2 hP'.2).trans ((D.naut.typeV_indep i).pairwiseDisjoint hne).le_bot))
  exact h2

theorem main : ∀ D : D7, GlobalTheory.NRows.PartsGive D := fun D => GlobalTheory.NRows.partsGive_of (h41 D) (h42 D)
end GlobalTheory.NRows.Parts
end
