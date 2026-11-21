import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowLocalAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalAwayFromTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSatakeOfUnr

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000
section SphOffSec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult
namespace GlobalTheory.RowSphOff
end GlobalTheory.RowSphOff
end SphOffSec
namespace GlobalTheory.RowSphOff
theorem spherical_localComponent_away_from_level_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (σ : (w.st Z).toD7.what₂.FT) (s : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E), (∀ k : Fin 2, s.w ∉ placesOver (w.st Z).toD7.host.E ((w.st Z).toD7.host.g k)) → ∃ τ, IsLocS (repOf Y σ).S s τ ∧ GlobalTheory.SmGL.IsSpherical τ.ρ := by
  intro hPr
  refine evG_all fun K => lg_all K fun B f T _ => ?_
  intro hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA σ s hoff
  obtain ⟨h, hh⟩ := levS_of_kO_conj _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins s hoff
  obtain ⟨φ, hφS, hφ0, hφfix⟩ := exists_fixed_of_level _ _ _ _ _ _ _ z.R z.F p0 Y σ
    {κ | ReciprocityTheory.Aut.TrivOutside {s.v} κ ∧ h⁻¹ * s.loc _ κ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield (w.st Z).toD7.host.E)) (Fin (w.st Z).toD7.R.r)}
    (fun b κ hκ => hh b κ hκ.1 hκ.2)
  obtain ⟨τ, hτ⟩ := exists_isLocS_rows hPr.hc hPr.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ s
  refine ⟨τ, hτ, ?_⟩
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq _ s h
  have hmul : ∀ (a b : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r) (g : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r → ℂ),
      NG.rt _ _ (a * b) g = NG.rt _ _ a (NG.rt _ _ b g) := by
    intro a b g
    funext c
    simp [NG.rt, mul_assoc]
  have hone : ∀ g : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r → ℂ, NG.rt _ _ 1 g = g := by
    intro g
    funext c
    simp [NG.rt]
  have hT : ∀ a b : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r, ReciprocityTheory.Aut.TrivOutside {s.v} a →
      ReciprocityTheory.Aut.TrivOutside {s.v} b → ReciprocityTheory.Aut.TrivOutside {s.v} (a * b) :=
    fun a b ha hb v hv => by
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha v hv, hb v hv, mul_one]
  refine fixed_kO_ne_bot _ _ (repOf Y σ) s τ hτ (NG.rt _ _ x⁻¹ φ) ((repOf Y σ).stable _ φ hφS) ?_ ?_
  · intro h0
    apply hφ0
    rw [← hone φ, ← mul_inv_cancel x, hmul, h0, map_zero]
  · intro κ hκ hk
    have h1 := hφfix (x * κ * x⁻¹) ⟨hT _ _ (hT _ _ hx hκ) (GlobalTheory.RowLevelSplit.trivOutside_inv hx), by
      rw [map_mul, map_mul, map_inv, e, show h⁻¹ * (h * s.loc _ κ * h⁻¹) * h = s.loc _ κ by group]
      exact hk⟩
    rw [← hmul, show κ * x⁻¹ = x⁻¹ * (x * κ * x⁻¹) by group, hmul, h1]
end GlobalTheory.RowSphOff
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spherical_loc_comp_at_split_place_off_g : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (σ : (w.st Z).toD7.what₂.FT) (s : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E), (∀ k : Fin 2, s.w ∉ placesOver (w.st Z).toD7.host.E ((w.st Z).toD7.host.g k)) → ∃ τ, IsLocS (repOf Y σ).S s τ ∧ GlobalTheory.SmGL.IsSpherical τ.ρ := by
  first | exact @_root_.GlobalTheory.RowSphOff.spherical_localComponent_away_from_level_alt | exact _root_.GlobalTheory.RowSphOff.spherical_localComponent_away_from_level_alt | (intros; apply _root_.GlobalTheory.RowSphOff.spherical_localComponent_away_from_level_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowSphSmall
open GlobalTheory.CuspRep.ParLaws GlobalTheory.LocLanglands
theorem reciprocity_unramified_and_norm_frobenius_eigenvalue_le (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {n : ℕ} (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))) (hs : GlobalTheory.SmGL.IsSpherical σ.ρ)
    (hu : GlobalTheory.SmGL.IsUnitarisable σ.ρ) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).unr ∧
      ∀ α ∈ (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).frobEig, ‖α‖ ≤ ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  have H := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  have hunr : (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).unr := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical H σ).2 hs
  refine ⟨hunr, ?_⟩
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt H hunr
  rw [_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake H hα, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  have h1 := GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake E w n (GlobalTheory.SplitRead.Irr.ofIrrRep σ) α hα hu
  have h2 : GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n
      ((Finset.univ.val.map fun i => (α i : ℂ)).map (·⁻¹)) := by
    have := GlobalTheory.RowSatakeBound.finite_residue w
    exact GlobalTheory.SatakeInv.isUnitarySatake_map_inv _ _ _ _ h1
  intro b hb
  apply h2.norm_le
  simpa [Multiset.map_map, Function.comp_def] using hb
end GlobalTheory.RowSphSmall
section FormSec
namespace GlobalTheory.RowSphSmall
end GlobalTheory.RowSphSmall
end FormSec
namespace GlobalTheory.RowSphSmall
end GlobalTheory.RowSphSmall
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowSphSmall
theorem spherical_localComponent_of_small_prime_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y =>
    ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ σ, RowLoc (w.st Z).toD7 Rw σ := by
  intro hP hL
  refine EvG.imp (_root_.GlobalTheory.T.exists_spherical_loc_comp_at_split_place_off_g hP) fun K _ _ _ _ hK => large₂.imp hK fun B f T _ H => ?_
  intro hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA Rw hPar σ w' hsplit hoff
  have H' := H hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA σ
  obtain ⟨s, rfl⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl _ w' hsplit
  obtain ⟨τ, hloc, hsph⟩ := H' s hoff
  obtain ⟨Bf, k1, k2, k3, k4⟩ := exists_form_rowRepR hP.hc hP.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  have hunit := isUnitarisable_of_isLocS (repOf Y σ) Bf k1 k2 k3 k4 s τ hloc
  have he := hPar.row.1 σ s τ hloc
  obtain ⟨hu, hb⟩ := _root_.GlobalTheory.RowSphSmall.reciprocity_unramified_and_norm_frobenius_eigenvalue_le hL ((w.st Z).toD7.nd.plOm.2 s.w) τ hsph hunit
  rw [← he] at hu hb
  have hu' := (hPar.T.unr _ _).2 hu
  refine ⟨hu', fun α hα => ?_⟩
  rw [hPar.T.frobEig _ _ hu'] at hα
  have h1 := hb α hα
  have hq : (1 : ℝ) < ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) := by exact_mod_cast GlobalTheory.WeilDeligne.one_lt_normV s.w
  have hrt : (((w.st Z).toD7.R.r : ℝ) - 1) / 2 < (((w.st Z).toD7.R.t : ℝ) - 1) / 2 := by
    have := (w.st Z).toD7.R.rank_add_five_le
    have h2 : (w.st Z).toD7.R.r < (w.st Z).toD7.R.t := by unfold Ranks.r; omega
    have h3 : ((w.st Z).toD7.R.r : ℝ) < ((w.st Z).toD7.R.t : ℝ) := by exact_mod_cast h2
    linarith
  calc ‖α‖ ≤ ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.r : ℝ) - 1) / 2) := h1
    _ < ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.t : ℝ) - 1) / 2) := Real.rpow_lt_rpow_of_exponent_lt hq hrt
    _ = ((Ideal.absNorm s.w.asIdeal : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.t : ℝ) - 1) / 2) := rfl
end GlobalTheory.RowSphSmall
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_of_par_in_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ σ, RowLoc (w.st Z).toD7 Rw σ := by
  first | exact @_root_.GlobalTheory.RowSphSmall.spherical_localComponent_of_small_prime_alt | exact _root_.GlobalTheory.RowSphSmall.spherical_localComponent_of_small_prime_alt | (intros; apply _root_.GlobalTheory.RowSphSmall.spherical_localComponent_of_small_prime_alt <;> assumption)
end
end
end
