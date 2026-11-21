import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PotentialCrystallinity.IsPotCrysAtOfMono0G
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParTwistAbsPow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.OpenUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsCusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SeparableConjugates.SepConjG
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Imports
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolCoeffZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem locParT_twist_absPow_eq_lpTw (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (π : CG E a)
    {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) :
    _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (π.twist ν) h = (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpTw s :=
  _root_.GlobalTheory.HeightCounting.Blocks.local_parameter_twist_abs_pow hL hF π hν h
end G
end GlobalTheory.HodgeOfTrue
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial
end GlobalTheory.HeightCounting
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial
end GlobalTheory.GalAllPlaces
end
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.CsdTwistGal
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
theorem weight_eq_alt_alt {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} {χ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT) (m : (E →+* ℂ) → Multiset ℂ) (s : ℝ)
    (hcard : ∀ τ, (m τ).card = a) (hinf : ∀ τ, (CG.mk π).infChar τ = (m τ).map (· + (s : ℂ)))
    (hconj : ∀ τ, m (ComplexEmbedding.conjugate τ) = (m τ).map Neg.neg) :
    (wt : ℝ) = (a : ℝ) - 1 - 2 * s := by
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ : ι.toRingHom.comp (ι.symm.toRingHom.comp τ0) = τ0 := by ext x; simp
  set τ : E →+* Qbar l := ι.symm.toRingHom.comp τ0 with hτdef
  set X : Multiset ℂ := (HT τ).map (fun n : ℤ => (n : ℂ)) with hXdef
  have hX : X = (m τ0).map (fun z => (((a : ℂ) - 1) / 2 - s) + (-1) * z) := by
    rw [hXdef, H.weights τ, hτ, hinf, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]; ring
  have hY : (HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).map (fun n : ℤ => (n : ℂ)) =
      X.map (fun z => (wt : ℂ) + (-1) * z) := by
    rw [H.weights_conj, hXdef, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun n _ => ?_
    simp only [Function.comp_apply]; push_cast; ring
  have hZ : (HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).map (fun n : ℤ => (n : ℂ)) =
      (m τ0).map (fun z => (((a : ℂ) - 1) / 2 - s) + 1 * z) := by
    rw [H.weights, comp_complexConj, hτ, hinf, hconj, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]; ring
  have hcX : (X.card : ℂ) = a := by rw [hX, Multiset.card_map, hcard]
  have e := congrArg Multiset.sum (hY.symm.trans hZ)
  rw [sum_map_affine, sum_map_affine, hcX, hX, sum_map_affine, hcard] at e
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have h : (wt : ℂ) = (a : ℂ) - 1 - 2 * (s : ℂ) := by
    apply mul_left_cancel₀ ha0
    linear_combination e
  exact_mod_cast h
end GlobalTheory.TempSatGal
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
section CharUnr
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
theorem locPar_ofChar_unr_and_frobEig (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h).unr ∧
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  have e2 : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, H.one]
    have hs := ha.smooth (ParLaws.isSmoothChar_loc χ w)
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  exact ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), by simp⟩
end CharUnr
section Twist
end Twist
section G
end G
end GlobalTheory.HodgeOfTrue
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.WeilDeligne
section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
variable {N A}
end
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
end
end UpperTheory.GalS
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp
variable (D : D7) (T : WDTie D.nd D.naut) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
variable {D T ι π s r}
end GlobalTheory.TripleLocal
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem exists_galois_character_crystalline_at_places (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hG : _root_.UpperTheory.GalS.CuspUAlt)
    (ι : Qbar l ≃+* ℂ) (ψ : HChar E) (hu : ∀ v, ψ.UnrAt v) (hr : ∀ τ, ∃ n : ℤ, expo ψ τ = n)
    (hp : ∃ χ, IsPolarized ((CuspSub.triv E (le_refl 1)).twist ψ) χ) :
    ∃ c : G E Ω →* (Qbar l)ˣ, Continuous c ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (B : ValuationSubring Ω) (g : G E Ω),
        IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g → ι (c g : Qbar l) = (((ψ.val w)⁻¹ : ℂˣ) : ℂ)) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
        IsCrysAt P Bw ((GeneralLinearGroup.scalar (Fin 1)).comp (c.comp (Dec (F := E) A).subtype)) := by
  obtain ⟨χ, hχ⟩ := hp
  have hreg : (CG.mk ((CuspSub.triv E (le_refl 1)).twist ψ)).IsRegAlg := (CG.isRegAlg_ofChar ψ).2 hr
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι 1 le_rfl _ χ hreg hχ
  have hcr : Continuous fun g => (r g : Matrix (Fin 1) (Fin 1) (Qbar l)) := Units.continuous_val.comp H.cont
  have hsc : (GeneralLinearGroup.scalar (Fin 1)).comp (Matrix.GeneralLinearGroup.det.comp r) = r := by
    ext g i j
    rw [MonoidHom.comp_apply, coe_scalar, Subsingleton.elim i 0, Subsingleton.elim j 0]
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    change Matrix.det (r g : Matrix (Fin 1) (Fin 1) (Qbar l)) = _
    rw [Matrix.det_fin_one]
  have hdet : Continuous fun x : GL (Fin 1) (Qbar l) => Matrix.GeneralLinearGroup.det x := GeneralLinearGroup.continuous_det
  refine ⟨MonoidHom.comp Matrix.GeneralLinearGroup.det r, hdet.comp H.cont, fun w hl B g hB hg => ?_, fun P AI hT w A h O _ _ _ Bw hj => ?_⟩
  · obtain ⟨y1, y2⟩ := _root_.GlobalTheory.HodgeOfTrue.locPar_ofChar_unr_and_frobEig hL ψ hB (hu w)
    have e1 : wdOf hB hl ι r = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar ψ) hB := by
      rw [H.eq_locPar hL hF hl hB y1, show (1 - ((1 : ℕ) : ℝ)) / 2 = 0 by norm_num, WD.lpTw_zero]
      rfl
    have f := frobEig_wdOf hl ι hcr (e1 ▸ y1) hB hg
    rw [e1, y2] at f
    have h1 : (r g : Matrix (Fin 1) (Fin 1) (Qbar l)).charpoly = X - C ((r g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0) := by
      simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]
    rw [h1] at f
    have f2 := congrArg (fun p => p.coeff 0) f
    simp at f2
    change ι (Matrix.det _) = _
    rw [Matrix.det_fin_one]
    exact f2.trans (Units.val_inv_eq_inv_val _).symm
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E 1 ((CuspSub.triv E (le_refl 1)).twist ψ) w
    have hc := (H.above P AI hT w A h O Bw hj).crys σ hσ ((_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) (ParLaws.toRep σ)).1 (by
      rw [← _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h]
      exact (_root_.GlobalTheory.HodgeOfTrue.locPar_ofChar_unr_and_frobEig hL ψ h (hu w)).1))
    have e : (GeneralLinearGroup.scalar (Fin 1)).comp ((Matrix.GeneralLinearGroup.det.comp r).comp (Dec (F := E) A).subtype) =
        r.comp (Dec (F := E) A).subtype := by
      rw [← MonoidHom.comp_assoc, hsc]
    rw [e]
    exact hc
end G
end GlobalTheory.HodgeOfTrue
namespace GlobalTheory.GalAway
end GlobalTheory.GalAway
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocGL GlobalTheory.HeightCounting GlobalTheory.HeightCounting.TrueSide UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
section Twist
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} [IsTotallyComplex E]
  (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
include hF in
theorem locPar_twist_alt (π : CG E a) (χ : HChar E) (h : IsPlaceOver A w)
    (hg : Good (⟨a, ParLaws.toCl (π.loc w)⟩ : IrrGL (w.adicCompletion E))) :
    _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (π.twist χ) h = (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpChar (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, _root_.GlobalTheory.CuspRep.ParLawsT.locParT, _root_.GlobalTheory.CuspRep.ParLawsT.locParT, cls_loc_twist]
  have _ := hF
  exact _root_.UpperTheory.One.M.LawsM.twist H _ _ _ hg
end Twist
namespace Old
end Old
namespace New
end New
end UpperTheory.One.M
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem llc_good_of_locPar_unr (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (π : CG E a) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    (h : IsPlaceOver A w) (hu : (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).unr) :
    UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl (π.loc w)⟩ : IrrGL (w.adicCompletion E)) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  exact (GlobalTheory.SphSupport.toral_and_good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz _ _ ((H.sph _).2 hu)).2
end G
end GlobalTheory.HodgeOfTrue
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem isPotCrysAt_of_mono0' (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : _root_.UpperTheory.GalS.CarUAlt)
    (hD : ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite → Dense {g : G E Ω | ∃ w ∉ S, ∃ B : ValuationSubring Ω,
      IsPlaceOver (F := E) B w ∧ IsFrob (F := E) B (normV w) g})
    {π₀ : CuspSub E a} (ha : 2 ≤ a) (hc : π₀.IsCsd) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s)
    {ξ : HChar E} (hξu : ∀ v, ξ.UnrAt v) (hξc : (CG.ofChar ξ).IsCsd) (hξc' : (CG.ofChar ξ⁻¹).IsCsd)
    (hreg : (CG.mk (π₀.twist ξ)).IsRegAlg) (hint : ∀ τ, ∃ n : ℤ, expo (ξ⁻¹ * ν) τ = n)
    {ι : Qbar l ≃+* ℂ} {χ : HChar (maximalRealSubfield E)} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : _root_.UpperTheory.GalS.IsGalUAlt (π₀.twist ν) χ ι r wt HT)
    {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E l)
    {A : ValuationSubring Ω} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
    (hm : UpperTheory.GalS.NcW (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) h))
    (hgood : UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl ((CG.mk π₀).loc w)⟩ : IrrGL (w.adicCompletion E))) :
    IsPotCrysAt P Bw (r.comp (Dec (F := E) A).subtype) := by
  have hc' : (π₀.twist ξ).IsCsd := CG.IsCsd.twist hξc (π := CG.mk π₀) hc
  obtain ⟨r₀, wt₀, HT₀, H₀, K₀⟩ := hGL E Ω l ι a ha _ hc' hreg
  have e0 : (π₀.twist ξ).twist (ξ⁻¹ * ν) = π₀.twist ν := by
    rw [← CuspSub.twist_mul, mul_inv_cancel_left]
  have hψu : ∀ v, (ξ⁻¹ * ν).UnrAt v := fun v => (hξu v).inv.mul (hν.1 v)
  have hp : ∃ χ', IsPolarized ((CuspSub.triv E (le_refl 1)).twist (ξ⁻¹ * ν)) χ' := by
    rw [CuspSub.twist_mul]
    exact isPolarized_twist hξc' hν
  obtain ⟨c, hcc, hcf, hcr⟩ := _root_.GlobalTheory.HodgeOfTrue.exists_galois_character_crystalline_at_places (Ω := Ω) hL hF hG ι (ξ⁻¹ * ν) hψu hint hp
  have hc0 : Continuous fun g => (r₀ g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H₀.cont
  have hc1 : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H.cont
  have hc2 : Continuous fun g => (twistBy c r₀ g : Matrix (Fin a) (Fin a) (Qbar l)) := by
    simp only [coe_twistBy]
    exact (Units.continuous_val.comp hcc).smul hc0
  obtain ⟨B, hBc⟩ := conj_of_frob hD hc1 hc2 H.ss (isSSRep_twistBy c H₀.ss) (by
    filter_upwards [eventually_natCast_notMem E l, _root_.GlobalTheory.CuspRep.ParLaws.eventually_unramified_local_parameter (Ω := Ω) hL hF (CG.mk (π₀.twist ξ))] with w hl hu Bp g hBp hg
    have e3 : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ν)) hBp =
        (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ξ)) hBp).lpChar (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar (ξ⁻¹ * ν)) hBp) := by
      rw [← e0]
      exact _root_.UpperTheory.One.M.locPar_twist_alt hL hF (CG.mk (π₀.twist ξ)) _ hBp (_root_.GlobalTheory.HodgeOfTrue.llc_good_of_locPar_unr hL _ hBp (hu _ hBp))
    obtain ⟨y1, y2⟩ := _root_.GlobalTheory.HodgeOfTrue.locPar_ofChar_unr_and_frobEig hL (ξ⁻¹ * ν) hBp (hψu w)
    have u1 := hu _ hBp
    have e1 := H.eq_locPar hL hF hl hBp (by rw [e3]; exact WD.unr_lpChar _ _ u1 y1)
    have e2 := H₀.eq_locPar hL hF hl hBp u1
    have u2 : (wdOf hBp hl ι r).unr := by rw [e1, e3, WD.unr_tw]; exact WD.unr_lpChar _ _ u1 y1
    have u3 : (wdOf hBp hl ι r₀).unr := by rw [e2, WD.unr_tw]; exact u1
    have f1 := frobEig_wdOf hl ι hc1 u2 hBp hg
    have f2 := frobEig_wdOf hl ι hc0 u3 hBp hg
    rw [e1, e3, WD.frobEig_tw _ _ (WD.unr_lpChar _ _ u1 y1), WD.frobEig_char _ _ _ u1 y1 y2] at f1
    rw [e2, WD.frobEig_tw _ _ u1] at f2
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [f1, coe_twistBy]
    have f3 : (((c g : Qbar l) • (r₀ g : Matrix (Fin a) (Fin a) (Qbar l))).charpoly.map ι.toRingHom) =
        ((ι (c g : Qbar l)) • ((r₀ g : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom)).charpoly := by
      rw [← Matrix.charpoly_map]
      congr 1
      ext i j
      simp
    rw [f3, GlobalTheory.Triple.charpoly_smul_of_prod _ _ _ (by rw [Matrix.charpoly_map]; exact f2), hcf w hl Bp g hBp hg]
    simp only [Multiset.map_map, Function.comp_def]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    congr 2
    ring)
  obtain ⟨σ₁, hσ₁, -⟩ := LocEx.exists_isLocComp hF E a (π₀.twist ξ) w
  have g2 : _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (algNorm σ₁) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ξ)) h).lpTw ((1 - (a : ℝ)) / 2) := by
    rw [_root_.GlobalTheory.GalOfCusp.rec_algNorm_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) σ₁]
    exact congrArg (fun x : WD h => x.lpTw _) (_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ₁ h).symm
  have hn : UpperTheory.GalS.NcW ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ξ)) h).lpTw ((1 - (a : ℝ)) / 2)) := by
    have e4 : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ξ)) h =
        (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) h).lpChar (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar ξ) h) :=
      _root_.UpperTheory.One.M.locPar_twist_alt hL hF (CG.mk π₀) ξ h hgood
    rw [e4]
    exact (hm.char (_root_.GlobalTheory.CuspRep.ParLaws.dim_local_parameter_eq_rank hL _ h) (_root_.GlobalTheory.HodgeOfTrue.locPar_ofChar_unr_and_frobEig hL ξ h (hξu w)).1).tw _
  have g1 := K₀ P AI ⟨T⟩ w hw A h O Bw hj σ₁ hσ₁ _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) (g2 ▸ hn)
  have hm' : (wdAt P ι Bw h hj (r₀.comp (Dec (F := E) A).subtype)).mono0 := g1.mono (g2 ▸ hn.2.1)
  have hab := H₀.above P AI ⟨T⟩ w A h O Bw hj
  have hpst := hB.isPstAt T Bw (r₀.comp (Dec (F := E) A).subtype) (H₀.cont.comp continuous_subtype_val |> Units.continuous_val.comp)
    (hab.deRham (_root_.UpperTheory.GalS.nice_of_loc_par hL hF h hn))
  have hpot := (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj P ι _ hpst).1 hm'
  have hpot2 := potCrys_twistBy T Bw (c.comp (Dec (F := E) A).subtype) (r₀.comp (Dec (F := E) A).subtype) hpot
    (hcr P AI ⟨T⟩ w A h O Bw hj)
  refine (GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ (r.comp (Dec (F := E) A).subtype) B⁻¹ (fun g => ?_)).2.2.1 hpot2
  have := hBc g
  change r g = B⁻¹ * twistBy c r₀ g * B⁻¹⁻¹
  rw [this]
  group
end G
end GlobalTheory.HodgeOfTrue
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
end G
theorem galHodge0_of_cgTrue (sw : _root_.UpperTheory.One.M.TrivialCondition) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : _root_.UpperTheory.GalS.CarUAlt)
    {D : D7} {T : WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) : UpperTheory.GalS.GalHodge0 D T := by
  intro l _ ι π s hc hr
  have := host_isCMField D.host
  have ha : 2 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (C.e _ π).1
  have hmk : CG.mk π₀ = (C.e _ π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (C.csd _ π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E s
  set ν := GlobalTheory.HeckeGal.Model.absPow D.host.E s
  have inf₁ : ∀ τ, (CG.mk (π₀.twist ν)).infChar τ = (D.naut.infG π τ).map (· + (s : ℂ)) := fun τ => by
    have h1 := (ParLaws.hasInfChar_infChar (CG.mk π₀) τ).twist ν
    rw [(GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ] at h1
    rw [C.inf, CGu.infChar, ← hmk]
    exact h1.infChar_eq
  have hreg : (CG.mk (π₀.twist ν)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    obtain ⟨h1, h2⟩ := hr τ
    rw [inf₁]
    refine ⟨h1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    exact h2 y hy
  obtain ⟨ψp, hP⟩ := isPolarized_twist hc₀ hν
  obtain ⟨r, wt, HT, H⟩ := hG _ D.nd.Om l ι _ (by omega) _ ψp hreg hP
  have hloc : ∀ (w : PlE D.host) (u : ℝ), T.e w (D.naut.lpTw (D.naut.locG π w) u) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [T.tw, C.loc, hmk]
    rfl
  have haway : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      UpperTheory.GalS.Aw (wdOf (D.nd.plOm.2 w) hl ι r) (T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (D.R.r : ℝ)) / 2))) := fun w hl => by
    have e := _root_.GlobalTheory.HodgeOfTrue.locParT_twist_absPow_eq_lpTw hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    have k := H.aw_locPar hL hF hl (D.nd.plOm.2 w)
    rw [show _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, WD.lpTw_add, ← hloc] at k
    exact k
  have hv : s + (1 - (D.R.r : ℝ)) / 2 + (wt : ℝ) / 2 = 0 := by
    have hm : ∀ τ, π₀.HasInfChar τ ((CG.mk π₀).infChar τ) := fun τ => ParLaws.hasInfChar_infChar (CG.mk π₀) τ
    have hw := _root_.GlobalTheory.TempSatGal.weight_eq_alt_alt (by omega) H (fun τ => (CG.mk π₀).infChar τ) s (fun τ => (hm τ).1)
      (fun τ => by rw [inf₁, C.inf, CGu.infChar, ← hmk])
      (fun τ => GlobalTheory.CsdTwistGal.infChar_conj_of_isCsd _ _ π₀ hc₀ τ _ _ (hm τ) (hm _))
    rw [hw]; ring
  have htemp : ∀ w : PlE D.host, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.unr (D.naut.locG π w) →
      ∀ α ∈ D.naut.frobEig (D.naut.locG π w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((D.R.r : ℝ) + 3) / 2) := fun w hl hu α hα => by
    obtain ⟨-, hU, hS⟩ := _root_.GlobalTheory.HeightCounting.Blocks.readsCusp_alt hF C
    obtain ⟨B, hB, e⟩ := hS _ π w (by omega) hu
    rw [e] at hα
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hα
    have k : UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) (b : ℂ) :=
      PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound D.host.E _ _ (hU _ π (by omega)) w B hB b hb
    rw [Units.val_inv_eq_inv_val]
    have hq := UpperTheory.GalN.one_lt_q (H := D.host) w
    refine (k.inv hq).2.le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq.le) ?_)
    have : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
    linarith
  refine ⟨r, ⟨Units.continuous_val.comp H.cont, H.ss, haway, htemp⟩, fun w hw O _ _ _ Bw hj => ?_⟩
  have hpar : T.e w (D.naut.locG π w) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w) := by
    rw [C.loc, hmk]
    rfl
  have hab := H.above (D.loc l) (D.locA l) ⟨D.locT l⟩ w _ (D.nd.plOm.2 w) O Bw hj
  have hN : UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) → _root_.UpperTheory.GalS.NiceAlt (π₀.twist ν) (D.nd.plOm.2 w) := fun k => by
    refine _root_.UpperTheory.GalS.nice_of_loc_par hL hF _ (UpperTheory.GalS.NcW.tw ?_ _)
    have e := _root_.GlobalTheory.HodgeOfTrue.locParT_twist_absPow_eq_lpTw hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    rw [show _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, ← hpar]
    exact (UpperTheory.GalS.ncW_of_nc T k).tw _
  refine ⟨fun k => ⟨hab.deRham (hN k), fun τ L τ' hτ => ⟨HT τ, ?_, hab.jumps (hN k) τ L τ' hτ⟩⟩, fun hu => ?_, fun hm => ?_⟩
  · rw [H.weights, inf₁, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    ring
  · obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hF _ _ (π₀.twist ν) w
    refine hab.crys σ₀ hσ₀ ((_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)) (ParLaws.toRep σ₀)).1 ?_)
    rw [← _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ₀ (D.nd.plOm.2 w)]
    have e := _root_.GlobalTheory.HodgeOfTrue.locParT_twist_absPow_eq_lpTw hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    rw [show _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, WD.unr_tw, ← hpar]
    exact (T.unr w _).1 hu
  · have hm' : UpperTheory.GalS.NcW (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)) := by
      rw [← hpar]
      exact UpperTheory.GalS.ncW_of_nc T hm
    have hgood : UpperTheory.Zero.LLC.Good (⟨D.R.r, ParLaws.toCl ((CG.mk π₀).loc w)⟩ : IrrGL (w.adicCompletion D.host.E)) := by
      rw [hmk]
      exact _root_.UpperTheory.One.M.New.cgGood sw C _ π w
    have hs2 : 2 * s = ((D.R.r : ℤ) - 1 - wt : ℤ) := by
      push_cast
      linarith
    have key : ∀ ξ : HChar D.host.E, (∀ τ, ∃ n : ℤ, expo ξ τ = (s : ℂ) + n) →
        (CG.mk (π₀.twist ξ)).IsRegAlg ∧ ∀ τ, ∃ n : ℤ, expo (ξ⁻¹ * ν) τ = n := fun ξ hξ => by
      refine ⟨(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, fun τ => ?_⟩
      · obtain ⟨h1, h2⟩ := hr τ
        obtain ⟨n, hn⟩ := hξ τ
        have e := ((ParLaws.hasInfChar_infChar (CG.mk π₀) τ).twist ξ).infChar_eq
        have e' : (CG.mk (π₀.twist ξ)).infChar τ = (D.naut.infG π τ).map (· + expo ξ τ) := by
          rw [C.inf, CGu.infChar, ← hmk]
          exact e
        rw [e']
        refine ⟨h1.map (add_left_injective _), fun z hz => ?_⟩
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
        obtain ⟨m, hm2⟩ := h2 y hy
        refine ⟨m + n, ?_⟩
        simp only [hn]
        push_cast
        linear_combination hm2
      · obtain ⟨n, hn⟩ := hξ τ
        refine ⟨-n, ?_⟩
        rw [expo_mul, expo_inv, hn, (GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ]
        push_cast
        ring
    have hD : ∀ S : Set (HeightOneSpectrum (𝓞 D.host.E)), S.Finite → Dense {g : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ S,
        ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) g} := fun S hS =>
      Dense.mono (by rintro g ⟨w, h1, -, h2⟩; exact ⟨w, h1, h2⟩)
        (GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 GlobalTheory.Published.chebotarevDegreeOne') S hS)
    obtain ⟨ξh, x1, x2, x3, x4⟩ := exists_halfChar D
    have hone : ∀ v, (1 : HChar D.host.E).UnrAt v := fun v x _ => rfl
    have cone : (CG.ofChar (1 : HChar D.host.E)).IsCsd := isCsd_ofChar_of_res _ _ (Or.inl
      ⟨fun v k => by
        simp only [HChar.resFin, MonoidHom.finset_prod_apply]
        exact Finset.prod_eq_one fun _ _ => rfl,
      fun v k => by
        simp only [HChar.resInf, MonoidHom.finset_prod_apply]
        exact Finset.prod_eq_one fun _ _ => rfl⟩)
    rcases Int.even_or_odd' ((D.R.r : ℤ) - 1 - wt) with ⟨k, hk | hk⟩
    · have hsk : (s : ℂ) = k := by
        rw [hk] at hs2
        push_cast at hs2
        have : s = k := by linarith
        rw [this]
        simp
      obtain ⟨k1, k2⟩ := key 1 fun τ => ⟨-k, by rw [CG.expo_one, hsk]; push_cast; ring⟩
      exact _root_.GlobalTheory.HodgeOfTrue.isPotCrysAt_of_mono0' hL hF hG hB hGL hD ha hc₀ hν (fun v => hone v) cone (by rwa [inv_one]) k1 k2 H (D.locT l) hw
        (D.nd.plOm.2 w) Bw hj hm' hgood
    · have hsk : (s : ℂ) = k + 1 / 2 := by
        rw [hk] at hs2
        push_cast at hs2
        have : s = k + 1 / 2 := by linarith
        rw [this]
        simp
      obtain ⟨k1, k2⟩ := key ξh fun τ => by
        obtain ⟨n, hn⟩ := x4 τ
        exact ⟨n - k, by rw [hn, hsk]; push_cast; ring⟩
      exact _root_.GlobalTheory.HodgeOfTrue.isPotCrysAt_of_mono0' hL hF hG hB hGL hD ha hc₀ hν x1 x2 x3 k1 k2 H (D.locT l) hw (D.nd.plOm.2 w) Bw hj hm' hgood
end GlobalTheory.HodgeOfTrue
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.L2.Host Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.HeightCounting GlobalTheory.SmGL GlobalTheory.SatakeFlip GlobalTheory.LocGL
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS
theorem sep_conj_g_alt (sw : _root_.UpperTheory.One.M.TrivialCondition) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7}
    {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) {a : ℕ} (π : D.naut.CG a) (hc : D.naut.csd π) {w w' : PlE D.host}
    (hw : IsConjPl D.host w w') (k : Sep D.nd D.naut (D.naut.locG π w)) : Sep D.nd D.naut (D.naut.locG π w') := by
  have := host_isCMField D.host
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (C.e _ π).1
  have hmk : CG.mk π₀ = (C.e _ π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (C.csd _ π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hpar : ∀ v, T.e v (D.naut.locG π v) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 v) := fun v => by
    rw [C.loc, hmk]
    rfl
  rw [sep_iff T, hpar] at k ⊢
  obtain ⟨γ, hγ⟩ := GlobalTheory.exists_tameGenAt_of_isPlaceOver _ _ _ _ (D.nd.plOm.2 w')
  obtain ⟨γ', ⟨c, hcE, hcA, -⟩, -⟩ := GlobalTheory.conjGen_transport_exists D w' w γ (GlobalTheory.TwistDet.isConjPl_symm hw) hγ
  have hcp : ConjPl (IsCMField.complexConj D.host.E).toRingEquiv w w' :=
    (conjPl_iff_mem _ _ _).2 fun x y e => hw x y (e.trans (host_complexConj D.host _))
  obtain rfl : w' = conjSrc (IsCMField.complexConj D.host.E).toRingEquiv w := eq_conjSrc fun x => by
    simpa using (hcp (IsCMField.complexConj D.host.E x)).symm
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF _ a π₀ w
  have good : ∀ (v : PlE D.host) (τ : SmIrr (GL (Fin a) (v.adicCompletion D.host.E))), π₀.IsLocComp v τ →
      UpperTheory.Zero.LLC.Good (cls (ParLaws.toRep τ)) := fun v τ hτ => by
    have g := _root_.UpperTheory.One.M.New.cgGood sw C _ π v
    have h1 : (CG.mk π₀).IsLoc v (Quotient.mk _ τ) := hτ
    rw [← hmk, CG.IsLoc.unique _ a _ v _ _ h1.loc h1] at g
    exact g
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ] at k
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL (ParLaws.isLocComp_flip hc₀ hσ)]
  let π₁ : IrrRep (GL (Fin a) (w.adicCompletion D.host.E)) :=
    ⟨σ.V, σ.ρ.comp (GlobalTheory.TypeTame.invTranspose a), fun v => (σ.smooth v).preimage (GlobalTheory.TypeTame.continuous_invTranspose a),
      GlobalTheory.GelfandKazhdan.isIrreducible_comp _ (fun g => ⟨_, GlobalTheory.TypeTame.invTranspose_invTranspose a g⟩) σ.irred⟩
  have hE := GlobalTheory.GelfandKazhdan.equiv_contra _ a σ.V σ.ρ
    (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top _ a σ.V σ.ρ σ.smooth σ.irred) σ.irred
  have hr := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)
  let cc := (IsCMField.complexConj D.host.E).toRingEquiv
  let i := RingEquiv.ofBijective (conjLoc cc w) ⟨(conjLoc cc w).injective, ParLaws.conjLoc_surjective cc w⟩
  let L := longElt a (w.adicCompletion D.host.E)
  obtain ⟨b', b, h1, h2, -, h4⟩ := _root_.UpperTheory.One.M.New.field hL (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (conjSrc cc w))) hr c
    (D.host.conj : D.host.E →+* D.host.E) i (fun z => (hcA z).symm) hcE (conjLoc_spec cc w).1
    (fun x => ((conjLoc_spec cc w).2.1 x).trans (congrArg _ (host_complexConj D.host x))) a
    (ParLaws.toRep ⟨σ.V, σ.ρ.comp (ParLaws.flip (conjLoc cc w) a),
        isSmooth_comp σ.smooth _ (ParLaws.continuous_flip (conjLoc_spec _ w).1),
        ParLaws.isIrreducible_comp σ.irred _ (ParLaws.flip_surjective (ParLaws.conjLoc_surjective _ w))⟩) π₁
    (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.ρ.asGroupHom L)) (fun g v => by
      change σ.ρ L (σ.ρ (invRevT (Matrix.GeneralLinearGroup.map (conjLoc cc w) g)) v) =
        σ.ρ (invT a _ (Matrix.GeneralLinearGroup.map (conjLoc cc w) g)) (σ.ρ L v)
      have e : ∀ (x y : GL (Fin a) (w.adicCompletion D.host.E)) (u : σ.V), σ.ρ x (σ.ρ y u) = σ.ρ (x * y) u :=
        fun x y u => by rw [map_mul]; rfl
      refine (e _ _ v).trans (Eq.trans ?_ (e _ _ v).symm)
      rw [ParLaws.invRevT_eq, inv_mul_cancel_right]) (good _ _ (ParLaws.isLocComp_flip hc₀ hσ))
  first | (have hOpn := UpperTheory.One.M.opn _ (hr); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := hr
  have kd := k.dual
  rw [← _root_.UpperTheory.One.M.LawsM.dual H a (ParLaws.toRep σ) π₁ (good _ _ hσ) hE, ← h2] at kd
  exact h1 ▸ kd.transport c (D.host.conj : D.host.E ≃+* D.host.E) hcE hcA h4
end UpperTheory.GalS
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.L2.Host Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.HeightCounting GlobalTheory.SmGL GlobalTheory.SatakeFlip GlobalTheory.LocGL
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
end
section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
variable {N A}
end
theorem tm_rankOne_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
    {C₀ : CharFrame D} (S : CharSide D C₀) (π : D.naut.CG 1) (w : PlE D.host) (ht : (S.e1 π).1.TameAt w) :
    Tm D.nd D.naut (D.naut.locG π w) := by
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (C.e 1 π)).1 with hχ'
  set χ := (S.e1 π).1 with hχ
  have hloc : ∀ v, T.e v (D.naut.locG π v) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [C.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [T.unr, hloc v]; exact _root_.GlobalTheory.RankOneComp.locParT_ofChar_unr_iff_unrAt hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (S.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := S.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [T.frobEig _ _ hv, hloc v]; exact _root_.GlobalTheory.RankOneComp.frobEig_locParT_ofChar_of_unrAt hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_inv, hf, mul_inv_cancel]
  rw [tm_iff T, hloc, hchar, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity]
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)
  rw [H.one]
  refine GlobalTheory.SerSys.LabDepth.tame_of_isTameWD ((PositivityTheory.LocalParametersCuspidal.DZC.tame_lpOfChar_iff _ _).2 fun σ hσ => ?_)
  exact GlobalTheory.MuTameQS.isTame_loc ht _ ((GlobalTheory.MuTameQS.val_lt_one_iff w _).2 (PositivityTheory.LocalParametersCuspidal.DZC.wild_to_unitsOne a ha σ hσ))
end UpperTheory.GalS
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.WeilDeligne
section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
variable {N A}
end
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
end
end UpperTheory.GalS
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp
variable (D : D7) (T : WDTie D.nd D.naut) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
variable {D T ι π s r}
end GlobalTheory.TripleLocal
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
end G
theorem _root_.UpperTheory.GalS.ghOf'_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : _root_.UpperTheory.GalS.CarUAlt)
    (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) (hl : LabTrue D T) : UpperTheory.GalS.GalHodgeN D T :=
  ⟨(_root_.GlobalTheory.HodgeOfTrue.galHodge0_of_cgTrue trivial) hL hF hG hB hGL C, GlobalTheory.T.full_degree_label_forces_trivial_wild_inertia D T hl, fun π hc _ _ hw k => (_root_.UpperTheory.GalS.sep_conj_g_alt trivial) hL hF C π hc hw k,
    fun _ S π w ht => _root_.UpperTheory.GalS.tm_rankOne_alt hL C S π w ht⟩
end GlobalTheory.HodgeOfTrue
namespace GlobalTheory.GalAway
end GlobalTheory.GalAway
end
end
end
