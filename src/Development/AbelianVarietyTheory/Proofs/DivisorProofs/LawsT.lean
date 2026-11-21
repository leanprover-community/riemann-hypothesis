import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalIffUnrOfLawsT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasSatakeOfUnrT

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep
  GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspRep.ParLawsT

theorem lpDim_locParT (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (π : CG E a) (h : IsPlaceOver A w) : (locParT hT π h).lpDim = a := by
  obtain ⟨_, _, H⟩ := isRecT_locRecT hT h
  exact H.dim _

end GlobalTheory.CuspRep.ParLawsT

end
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspRep.ParLawsT

theorem eventually_unrT : ∀ (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (π : CG E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), (locParT hT π h).unr := by
  intro hF hT E Ω _ _ _ _ _ _ a π
  induction π using Quotient.inductionOn with | _ π =>
  filter_upwards [LocSph.locComp_spherical E a π] with w hw A h
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨v, h0, hv⟩ := hw σ hσ
  obtain ⟨ah, hah, H⟩ := isRecT_locRecT hT h
  have e : locParT hT (Quotient.mk _ π) h = locRecT hT h (cls (ParLaws.toRep σ)) := by
    have h1 : CG.IsLoc (Quotient.mk _ π : CG E a) w (Quotient.mk _ σ) := hσ
    unfold locParT
    rw [CG.IsLoc.unique E a _ w _ _ h1.loc h1]
    rfl
  rw [e]
  refine (GlobalTheory.RecT.isSpherical_iff_unr_of_lawsT E Ω A w h ah hah _ ((GlobalTheory.RecT.lawsT_iff ah hah _).2 H) _).1 ?_
  refine fixed_ne_bot_of_equiv (equivRep (ParLaws.toRep σ)) ((Submodule.ne_bot_iff _).2 ⟨v, fun x => ?_, h0⟩)
  obtain ⟨x, hx⟩ := x
  rw [SphCompletion.KO_completion] at hx
  obtain ⟨g, rfl⟩ := hx
  exact (hv g).trans (one_smul _ _).symm

end GlobalTheory.CuspRep.ParLawsT
end
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions GlobalTheory.CuspRep.ParLaws
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CuspRep.ParLawsT

theorem lawsT : ∀ (hT : UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {R : Ranks}
    (H : Formalism.BasicNotions.Host R) (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (pl : Formalism.GaloisCohomology.Places H.E Ω),
    haveI := host_isCMField H
    (∀ {a} (π : HostCGu H a) w, (locGT hT pl π w).lpDim = a) ∧
    (∀ {a} (π : HostCGu H a), ∀ᶠ w in Filter.cofinite, (locGT hT pl π w).unr) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1) w,
      UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl (π.1.loc w)⟩ : IrrGL (w.adicCompletion H.E)) → locGT hT pl (π.tw χ) w = (locGT hT pl π w).lpChar (locGT hT pl χ w)) ∧
    (∀ {a} (π : HostCGu H a) τ, Multiset.card (π.infChar τ) = a) ∧
    (∀ {a} (π : HostCGu H a), π.IsRegAlg ↔ ∀ τ, (π.infChar τ).Nodup ∧
      ∀ z ∈ π.infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1) τ (s : ℂ), χ.infChar τ = {s} →
      (π.tw χ).infChar τ = (π.infChar τ).map (· + s)) ∧
    (∀ {a} (π : HostCGu H a) (χ : HostCGu H 1), χ.IsCsd → π.IsCsd → (π.tw χ).IsCsd) ∧
    (∀ {a} (π : HostCGu H a) w w', π.IsCsd → IsConjPl H w w' → (locGT hT pl π w).unr →
      (locGT hT pl π w').unr ∧ (locGT hT pl π w').frobEig = (locGT hT pl π w).frobEig.map (·⁻¹)) ∧
    (∀ (Q : Type) [Field Q] (ι : Q ≃+* ℂ) {a} (π : HostCGu H a) (τ : H.E →+* Q), π.IsRegAlg →
      (jumpsInf ι π τ).map (fun n : ℤ => (n : ℂ)) =
        (π.infChar (ι.toRingHom.comp τ)).map fun z => -z + ((a : ℂ) - 1) / 2) ∧
    ∀ (Q : Type) [Field Q] (ι : Q ≃+* ℂ) (n : ℕ) (wt : (H.E →+* ℂ) → Multiset ℂ) (τ : H.E →+* Q),
      ((jumpsWt ι n wt τ).map (fun n : ℤ => (n : ℂ)) =
        (wt (ι.toRingHom.comp τ)).map fun z => -z + ((n : ℂ) - 1) / 2) ↔
      ∀ z ∈ wt (ι.toRingHom.comp τ), ∃ m : ℤ, z = (m : ℂ) + ((n : ℂ) - 1) / 2 := by
  intro hT hF R H Ω _ _ _ pl
  have := host_isCMField H
  refine ⟨fun π w => lpDim_locParT hT _ _ _ _ _ π.1 _,
    fun π => (eventually_unrT hF hT _ Ω _ π.1).mono fun w hw => hw _ _,
    fun π χ w hg => ?_, fun π τ => π.1.card_infChar τ, fun π => GlobalTheory.CuspRep.CG.isRegAlg_iff _,
    fun π χ τ s => infChar_tw π.1 χ.1 τ s, fun π χ hχ hπ => CG.IsCsd.twist (χ.ofChar_equivChar.symm ▸ hχ) hπ,
    fun π w w' hπ hc => csd_unrT hT hF _ Ω _ π.1 hπ _ _
      ((conjPl_iff_mem _ _ _).2 fun x y e => hc x y (e.trans (host_complexConj H _))) _ _ _ _,
    fun Q _ ι a π τ h => map_jumps (h _).2, fun Q _ ι n wt τ => ⟨fun h => ((map_jumps_iff _).1 h).1, map_jumps⟩⟩
  show locParT hT (π.1.tw χ.1) _ = (locParT hT π.1 _).lpChar (locParT hT χ.1 _)
  rw [CG.tw, locParT_twist hF hT _ Ω _ _ _ π.1 _ _ hg, CG.ofChar_toChar]

end GlobalTheory.CuspRep.ParLawsT

end
end
