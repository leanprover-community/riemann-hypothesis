import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExAllOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoldsSDRAllOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoldsCsdCrysOfHoldsS
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoldsSGoodDROfCsd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedGoodOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineAllOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusAllOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusGoodOfSelfDual

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut

theorem exists_place_dvd_prime {K : Type} [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have hP : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(l : ℤ)}) ⊥
    (by
      intro x hx
      have : x = 0 := (algebraMap ℤ (𝓞 K)).injective_int (by simpa using hx)
      simp [this])
  have hmem : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQc ▸ Ideal.mem_span_singleton_self _
    simpa using this
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((l : ℕ) : 𝓞 K) = 0 := by simpa using hmem
    have : ((l : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hl.out.ne_zero
    exact this h0
  exact ⟨⟨Q, hQ, hne⟩, hmem⟩

theorem continuous_tw_of_continuous {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {k : Type} [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {n : ℕ} {r : Γ →* GL (Fin n) k} {μ : Γ →* kˣ} (hr : Continuous r) (hμ : Continuous μ) :
    Continuous (UpperTheory.V.Af.tw r μ) := by
  have h1 : Continuous fun s => (UpperTheory.V.Af.tw r μ s).val := by
    simp only [UpperTheory.V.Af.tw_val]
    exact (Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  simp only [← map_inv]
  exact h1.comp continuous_inv

theorem ex_good_of_ex_csd : AutomorphicFormsFiniteGL → Ex .csd → Ex .good := by
  intro hA hcsd E Ω _ _ _ _ _ _ l _ ι a ha π χ hs
  obtain ⟨w₀, hw₀⟩ := exists_place_dvd_prime (K := E) l
  have hsplit : GlobalTheory.UnitaryBC.IsSplitAt w₀ := by
    by_contra h
    exact (hs.2.2.2.2 w₀ h).1 hw₀
  obtain ⟨κ, m, hκ, -, hs'⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hA E l a ha π χ hs w₀ hsplit
  obtain ⟨r', hr'c, hr'⟩ := hcsd E Ω l ι a ha (π.twist κ) _ hs'
  have hκi : (κ⁻¹).IsAlg (-m) := fun k => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hκ k, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  obtain ⟨art, hart, hμ⟩ := (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hμ l ι κ⁻¹ (-m) (isAlgPos_of_isAlg hκi)
  refine ⟨UpperTheory.V.Af.tw r' μ, continuous_tw_of_continuous hr'c hμc, ?_⟩
  have h := UpperTheory.V.Af.Cq.attTwist E Ω l ι a r' (π.twist κ) hr' art κ⁻¹ (-m) μ hart hμ
  rwa [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] at h

end GlobalTheory.GalCut
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_good_of_self_dual : Inputs → SphericalLevelCondition .csd .unr → SphericalLevelCondition .good .unr := by
  first | (exact @GlobalTheory.RoadU.holdsS_good_unr) | (exact GlobalTheory.RoadU.holdsS_good_unr) | (intros; apply GlobalTheory.RoadU.holdsS_good_unr  <;> assumption)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_all_of_good : Inputs → SphericalLevelCondition .good .crys → SphericalLevelCondition .all .crys := by
  first | (exact @GlobalTheory.RoadU.holdsS_all_crys) | (exact GlobalTheory.RoadU.holdsS_all_crys) | (intros; apply GlobalTheory.RoadU.holdsS_all_crys  <;> assumption)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_all_of_good : Inputs → SphericalLevelCondition .good .crys → SphericalLevelCondition .good .phi → SphericalLevelCondition .all .phi := by
  first | (exact @GlobalTheory.RoadU.holdsS_all_phi) | (exact GlobalTheory.RoadU.holdsS_all_phi) | (intros; apply GlobalTheory.RoadU.holdsS_all_phi  <;> assumption)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_good_of_self_dual : Inputs → SphericalLevelCondition .csd .crys → SphericalLevelCondition .csd .phi → SphericalLevelCondition .good .phi := by
  first | (exact @GlobalTheory.RoadU.holdsS_good_phi) | (exact GlobalTheory.RoadU.holdsS_good_phi) | (intros; apply GlobalTheory.RoadU.holdsS_good_phi  <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem coreAll_of_core : Inputs → Core → CoreAll := by
  intro hI hC
  obtain ⟨hex, hh⟩ := hC
  have exg : Ex .good := GlobalTheory.GalCut.ex_good_of_ex_csd GlobalTheory.automorphicFormsFiniteGL hex
  have unrg : SphericalLevelCondition .good .unr := GlobalTheory.T.unramified_good_of_self_dual hI (hh .unr)
  have crysg : SphericalLevelCondition .good .crys := holdsS_good_crys hI (hh .crys)
  refine ⟨ex_all_of_good hI exg unrg, ?_⟩
  intro c
  cases c with
  | unr => exact GlobalTheory.UnrDescent.main hI unrg
  | dR => exact holdsS_dR_all_of_good hI (holdsS_good_dR_of_csd hI (hh .dR))
  | crys => exact GlobalTheory.T.crystalline_all_of_good hI crysg
  | phi => exact GlobalTheory.T.frobenius_all_of_good hI crysg (GlobalTheory.T.frobenius_good_of_self_dual hI (hh .crys) (hh .phi))

example : Inputs → Core → CoreAll := coreAll_of_core

end GlobalTheory.RoadU

end
end
