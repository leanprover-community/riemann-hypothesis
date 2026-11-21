import Formalism.AdmissibleDesigns.TheoremFromNormalizedOpenThree
import Formalism.AdmissibleDesigns.KoEquivSmul
import Formalism.AdmissibleDesigns.H1MapMemLcH1
import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
import Formalism.AdmissibleDesigns.DisplayForms
import Formalism.AdmissibleDesigns.CycMatchRec
import Formalism.AdmissibleDesigns.TwistedTargetOfInputs
import Formalism.AdmissibleDesigns.MsContW
import Formalism.AdmissibleDesigns.TrivialBoundTargetOfDict
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.AdmissibleDesigns.CoefChangeRec
import Formalism.AdmissibleDesigns.FiniteClassesLocalEq

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

def CycW : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (g : Dw i dc (idx i dc w)),
    (((Br.PD D.loc D.nbr i w hw).χ (eW i dc hw g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) =
      (((cycE i (g : GE D.nd) : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) : ℚ_[D.nd.l i])

def sE (e : ℕ) (g : GE D.nd) : D.nd.O i :=
  ((((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp (cycE i ^ (-(e : ℤ)))) g : (D.nd.O i)ˣ) : D.nd.O i)

def epsL {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) : Br.Ow (D.nbr i w hw) :=
  (D.nbr i w hw).eO (algebraMap ℤ_[D.nd.l i] (D.nd.O i) (((cycE i ((eW i dc hw).symm h : GE D.nd))⁻¹ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]))

end Rec

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem algZ_LL {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (z : ℤ_[D.nd.l i]) :
    algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) ((D.nbr i w hw).eO (algebraMap ℤ_[D.nd.l i] (D.nd.O i) z)) =
      algebraMap ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw)) (z : ℚ_[D.nd.l i]) := by
  rw [(D.nbr i w hw).eO_alg z, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ_[D.nd.l i] ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw))]
  rfl

theorem epsL_eq (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) :
    algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h) =
      algebraMap ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw))
        ((((Br.PD D.loc D.nbr i w hw).χ h)⁻¹ : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) := by
  have hc := hcyc w hw ((eW i dc hw).symm h)
  rw [MulEquiv.apply_symm_apply] at hc
  rw [epsL, algZ_LL, Units.val_inv_eq_inv_val, hc]
  congr 1
  exact eq_inv_of_mul_eq_one_left (by rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one])

variable [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def uRec {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) :
    Mc i Dd c ≃+ ((Fin 1 → Br.LLw (D.nbr i w hw)) ⧸ Formalism.MainNotions.N.stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) 1) :=
  φ.toAddEquiv.trans (koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw)) (fun c => Br.toLLK_alg (D.nbr i w hw) c))

theorem uRec_apply {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) (m : Mc i Dd c) :
    uRec i Dd hw c φ m =
      koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw)) (fun c => Br.toLLK_alg (D.nbr i w hw) c) (φ m) :=
  rfl

end Dict

section Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem yLoc_of
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (c : Fin (D.R.t + 1)) (n : ℕ) :
    YLoc (O := D.nd.O i) (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc n) := by
  intro ψ _
  let _ := Formalism.MainNotions.N.K.Topo.fracTopology (D.nd.O i)
  let _ := Formalism.MainNotions.N.K.Topo.rTopology (D.nd.O i) Dd.R'
  have := Formalism.MainNotions.N.K.Topo.fracTop_addGroup_O i
  have := Formalism.MainNotions.N.K.Topo.fracTop_smul_O i
  have := Formalism.MainNotions.N.K.Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  have := Formalism.MainNotions.N.K.Topo.rTop_constSMul_RD i Dd
  have := Formalism.MainNotions.N.K.Topo.rTop_mul_RD i r π g0 eB e₁ s Dd hD
  have h := Formalism.RepresentationBoundsCohomology.FIN.lc_of_torsion (D.nd.l i) Dd.r Dd.χ Dd.E (Formalism.MainNotions.N.K.Topo.padicCoeff_O i)
    (Formalism.MainNotions.N.K.Topo.fgTop_RD i r π g0 eB e₁ s Dd hD) (Formalism.MainNotions.N.K.Topo.uElt_cont i r π g0 eB e₁ s Dd hD hc)
    (fun m => Formalism.RepresentationBoundsCohomology.FIN.pi_ko_torsion (D.nd.O i) _ m) ψ
  exact h.comp_continuous continuous_subtype_val

end Loc

end Formalism.MainNotions.N.K.TBb

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem uRec_smul {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) (a : D.nd.O i) (m : Mc i Dd c) :
    uRec i Dd hw c φ (a • m) = (D.nbr i w hw).eO a • uRec i Dd hw c φ m := by
  rw [uRec_apply, uRec_apply]
  exact (congrArg (koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw))
    (fun x => Br.toLLK_alg (D.nbr i w hw) x)) (φ.map_smul a m)).trans (koEquiv_smul _ _ _ _ _)

theorem uRep_apply' (c : Fin (D.R.t + 1)) (g : GE D.nd) (m : Mc i Dd c) :
    uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m = uElt Dd.r Dd.χ g • m := rfl

omit [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem koE_apply' (e : ℕ) (g : GE D.nd) (x : KO (D.nd.O i)) : koE i e g x = sE i e g • x := rfl

theorem eO_sE (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (e : ℕ) (g : Dw i dc (idx i dc w)) :
    (D.nbr i w hw).eO (sE i e (g : GE D.nd)) = (epsL i dc hw (eW i dc hw g)) ^ e := by
  have hz : (cycE i ^ (-(e : ℤ))) (g : GE D.nd) = ((cycE i (g : GE D.nd))⁻¹) ^ e := by
    rw [show (cycE i ^ (-(e : ℤ))) (g : GE D.nd) = (cycE i (g : GE D.nd)) ^ (-(e : ℤ)) from rfl,
      zpow_neg, zpow_natCast, inv_pow]
  have key : sE i e (g : GE D.nd) = (algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      (((cycE i (g : GE D.nd))⁻¹ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i])) ^ e := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hz]
    rfl
  rw [key, map_pow]
  simp [epsL]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem uRec_act (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i))
    (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m) = koE i ((c : ℕ) - 1) g (φ m))
    (g : Dw i dc (idx i dc w)) (m : Mc i Dd c) :
    uRec i Dd hw c φ (uElt Dd.r Dd.χ (g : GE D.nd) • m) =
      (epsL i dc hw (eW i dc hw g)) ^ ((c : ℕ) - 1) • uRec i Dd hw c φ m := by
  have h1 : uElt Dd.r Dd.χ (g : GE D.nd) • m = sE i ((c : ℕ) - 1) (g : GE D.nd) • m := by
    apply φ.injective
    rw [← uRep_apply' i Dd c, hφ, koE_apply', φ.map_smul]
  rw [h1, uRec_smul, eO_sE i dc hcyc hw]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def coefDictOf (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i))
    (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m) = koE i ((c : ℕ) - 1) g (φ m))
    (hcont : Continuous fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^ ((c : ℕ) - 1)) :
    CoefDict (Br.PD D.loc D.nbr i w hw) (Br.LLw (D.nbr i w hw)) (Br.Ow (D.nbr i w hw)) (D.nbr i w hw).eO
      (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1) where
  Ce := twLat Subtype.val_injective (epsL i dc hw) (epsL_eq i dc hcyc hw) ((c : ℕ) - 1) hcont
  u := uRec i Dd hw c φ
  u_smul a m := uRec_smul i Dd hw c φ a m
  u_act g m := (uRec_act i dc Dd hcyc hw c φ hφ g m).trans
    (actD_twLat Subtype.val_injective (epsL i dc hw) (epsL_eq i dc hcyc hw) ((c : ℕ) - 1) hcont (eW i dc hw g)
      (uRec i Dd hw c φ m)).symm

end Dict

end Formalism.MainNotions.N.K.TBb

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB

section LenGen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {O' : Type} [CommRing O'] {σ : O' ≃+* O}
    {A T' GG : Type} [Ring A] [Algebra O' A] [CommRing T'] [Algebra T' A] [Group GG]
    {M : Type} [AddCommGroup M] [Module A M] [Module O' M] [SMulCommClass A O' M]
    {r : GG →* A} {χ : GG →* T'ˣ} {Dw : Subgroup GG} {eG : Dw ≃* G} {e : ℕ}
    (Cd : CoefDict PD LL O σ M r χ Dw eG e)

theorem trC_add (z₁ z₂ : Dw → M) : trC Cd (z₁ + z₂) = trC Cd z₁ + trC Cd z₂ := by
  funext g
  simp only [trC, Pi.add_apply, map_add]

theorem trC_sub (z₁ z₂ : Dw → M) : trC Cd (z₁ - z₂) = trC Cd z₁ - trC Cd z₂ := by
  funext g
  simp only [trC, Pi.sub_apply, map_sub]

theorem trC_smul (a : O') (z : Dw → M) : trC Cd (a • z) = σ a • trC Cd z := by
  funext g
  simp only [trC, Pi.smul_apply, Cd.u_smul]

theorem trC_apply_eG (z : Dw → M) (g : Dw) : trC Cd z (eG g) = Cd.u (z g) := by
  simp only [trC, MulEquiv.symm_apply_apply]

variable [TopologicalSpace Dw] (heG : Continuous eG.symm)

include heG in
theorem trC_Z1D' (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M)) :
    trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L := by
  unfold divisibleCocycles
  refine ⟨(hz.comp_continuous heG).comp Cd.u, fun g h => ?_⟩
  have hc0 := z.2
  unfold coZ1s at hc0
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hc0
  have hc : (z : Dw → M) (eG.symm g * eG.symm h) =
      (z : Dw → M) (eG.symm g) + uElt r χ ((eG.symm g : Dw) : GG) • (z : Dw → M) (eG.symm h) :=
    hc0 _ _
  show Cd.u ((z : Dw → M) (eG.symm (g * h))) =
    Cd.u ((z : Dw → M) (eG.symm g)) + actD Cd.Ce.L g (Cd.u ((z : Dw → M) (eG.symm h)))
  rw [map_mul eG.symm g h, hc, map_add, Cd.u_act, MulEquiv.apply_symm_apply]

variable (F : Submodule O' (H1z (resRep (uRep O' (M := M) r χ) Dw))) (ℓ cB : ℕ)

def rep (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    coZ1s (resRep (uRep O' (M := M) r χ) Dw) :=
  Classical.choose (Submodule.mem_map.1 y.2.1)

theorem rep_lc (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    IsLocallyConstant ((rep F ℓ cB y : coZ1s _) : Dw → M) := (Classical.choose_spec (Submodule.mem_map.1 y.2.1)).1

theorem rep_mk (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    (Submodule.mkQ _ (rep F ℓ cB y) : H1z (resRep (uRep O' (M := M) r χ) Dw)) = y := (Classical.choose_spec (Submodule.mem_map.1 y.2.1)).2

variable {F ℓ cB}
variable (hp : PD.p = ℓ)
  (hW : ∀ z : coZ1s (resRep (uRep O' (M := M) r χ) Dw), IsLocallyConstant (z : Dw → M) →
    (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F → trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L)
  (hB : ∀ z : coZ1s (resRep (uRep O' (M := M) r χ) Dw), IsLocallyConstant (z : Dw → M) →
    trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L → (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F)

include heG hW in
theorem diff_mem (z₁ z₂ : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (h₁ : IsLocallyConstant (z₁ : Dw → M))
    (h₂ : IsLocallyConstant (z₂ : Dw → M))
    (hF : (Submodule.mkQ _ z₁ : H1z (resRep (uRep O' (M := M) r χ) Dw)) - Submodule.mkQ _ z₂ ∈ F) :
    trC Cd (z₁ : Dw → M) - trC Cd (z₂ : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L := by
  have hlc : IsLocallyConstant (((z₁ - z₂ : coZ1s _) : Dw → M)) := h₁.sub h₂
  have hF' : (Submodule.mkQ _ (z₁ - z₂) : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F := by
    rw [map_sub]; exact hF
  have e : trC Cd ((z₁ - z₂ : coZ1s _) : Dw → M) = trC Cd (z₁ : Dw → M) - trC Cd (z₂ : Dw → M) := by
    rw [← trC_sub]; rfl
  rw [← e]
  exact Submodule.mem_inf.2 ⟨trC_Z1D' Cd heG _ hlc, hW _ hlc hF'⟩

include heG hW hp in
theorem rep_memQ (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M) ∈ QrecS PD Cd.Ce cB := by
  refine Submodule.mem_inf.2 ⟨trC_Z1D' Cd heG _ (rep_lc F ℓ cB y), ?_⟩
  rw [Submodule.mem_comap]
  have hlc : IsLocallyConstant ((((ℓ : O') ^ cB • rep F ℓ cB y : coZ1s _)) : Dw → M) :=
    (rep_lc F ℓ cB y).comp fun m => ((ℓ : O') ^ cB) • m
  have hmem : (Submodule.mkQ _ ((ℓ : O') ^ cB • rep F ℓ cB y) : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F := by
    rw [map_smul, rep_mk]
    first
      | exact y.2.2
      | simpa [divBy] using y.2.2
  have h := hW _ hlc hmem
  have e : trC Cd ((((ℓ : O') ^ cB • rep F ℓ cB y : coZ1s _)) : Dw → M) =
      σ ((ℓ : O') ^ cB) • trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M) := by
    rw [← trC_smul]; rfl
  rw [e] at h
  simpa [hp, map_pow, map_natCast] using h

def lenPre : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)) →ₛₗ[σ.toRingHom]
    Qrec PD Cd.Ce cB where
  toFun y := Submodule.Quotient.mk ⟨trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M), rep_memQ Cd heG hp hW y⟩
  map_add' y₁ y₂ := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    show trC Cd ((rep F ℓ cB (y₁ + y₂) : coZ1s _) : Dw → M) -
      (trC Cd ((rep F ℓ cB y₁ : coZ1s _) : Dw → M) + trC Cd ((rep F ℓ cB y₂ : coZ1s _) : Dw → M)) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L
    rw [← trC_add]
    refine diff_mem Cd heG hW (rep F ℓ cB (y₁ + y₂)) (rep F ℓ cB y₁ + rep F ℓ cB y₂) (rep_lc F ℓ cB _)
      ((rep_lc F ℓ cB y₁).add (rep_lc F ℓ cB y₂)) ?_
    rw [map_add, rep_mk, rep_mk, rep_mk, Submodule.coe_add, sub_self]
    exact F.zero_mem
  map_smul' a y := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    show trC Cd ((rep F ℓ cB (a • y) : coZ1s _) : Dw → M) -
      σ a • trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L
    rw [← trC_smul]
    refine diff_mem Cd heG hW (rep F ℓ cB (a • y)) (a • rep F ℓ cB y) (rep_lc F ℓ cB _)
      ((rep_lc F ℓ cB y).comp fun m => a • m) ?_
    rw [map_smul, rep_mk, rep_mk, Submodule.coe_smul, sub_self]
    exact F.zero_mem

include heG hp hW hB in

theorem lenMap_gen : LenMap PD σ
    (↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)) ⧸
      F.comap (Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)).subtype) Cd.Ce cB := by
  have key : ∀ y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)), lenPre (F := F) (ℓ := ℓ) (cB := cB) Cd heG hp hW y = 0 ↔ (y : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F := by
    intro y
    show Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      have h2 := hB _ (rep_lc F ℓ cB y) (Submodule.mem_inf.1 h).2
      rwa [rep_mk] at h2
    · intro h
      exact Submodule.mem_inf.2 ⟨trC_Z1D' Cd heG _ (rep_lc F ℓ cB y),
        hW _ (rep_lc F ℓ cB y) (by rw [rep_mk]; exact h)⟩
  have hle : F.comap (Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)).subtype ≤
      LinearMap.ker (lenPre (F := F) (ℓ := ℓ) (cB := cB) Cd heG hp hW) := fun y hy => LinearMap.mem_ker.2 ((key y).2 hy)
  refine ⟨(Submodule.liftQ _ (lenPre (F := F) (ℓ := ℓ) (cB := cB) Cd heG hp hW) hle).toAddMonoidHom, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [LinearMap.toAddMonoidHom_coe, Submodule.liftQ_apply] at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 ((key y).1 hx)
  · intro a x
    rw [LinearMap.toAddMonoidHom_coe]
    exact map_smulₛₗ _ a x

theorem trivial_bound_general {t cB : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (het : e < t) (Ce : TwLat PD LL O e) :
    (0 < e → divisibleCocycles Ce.L ⊓ HfD PD Ce.L ≤ BD Ce.L) ∧
      (e = 0 → divisibleCocycles Ce.L ⊓ HfD PD Ce.L = divisibleCocycles Ce.L ⊓ (Z1urD Ce.L I ⊔ BD Ce.L)) := by
  have h := hTB.2 e het Ce.V Ce.ρ Ce.L Ce.cont Ce.mat
  exact ⟨h.1, h.2.1⟩

end LenGen

section Conds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {O' : Type} [CommRing O'] {σ : O' ≃+* O}
    {A T' GG : Type} [Ring A] [Algebra O' A] [CommRing T'] [Algebra T' A] [Group GG]
    {M : Type} [AddCommGroup M] [Module A M] [Module O' M] [SMulCommClass A O' M]
    {r : GG →* A} {χ : GG →* T'ˣ} {Dw : Subgroup GG} {eG : Dw ≃* G} {e : ℕ}
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) [TopologicalSpace Dw] (heG : Continuous eG.symm)

theorem hW_bot (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (_hz : IsLocallyConstant (z : Dw → M))
    (h : (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ (⊥ : Submodule O' _)) :
    trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L := by
  refine Submodule.mem_sup_right ?_
  rw [Submodule.mem_bot] at h
  have h2 := (Submodule.Quotient.mk_eq_zero _).1 h
  rw [Submodule.mem_comap] at h2
  unfold coB1 at h2
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 h2
  have hz : ∀ g : Dw, (z : Dw → M) g = uElt r χ (g : GG) • m - m := fun g => (congrFun hm g).symm
  unfold BD
  refine LinearMap.mem_range.2 ⟨Cd.u m, ?_⟩
  funext x
  show actD Cd.Ce.L x (Cd.u m) - Cd.u m = Cd.u ((z : Dw → M) (eG.symm x))
  rw [hz, map_sub, Cd.u_act, MulEquiv.apply_symm_apply]

include heG in
theorem hB_bot (hpos : divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L ≤ BD Cd.Ce.L)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M))
    (h : trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L) :
    (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ (⊥ : Submodule O' _) := by
  have hZ := trC_Z1D' Cd heG z hz
  have hB := hpos (Submodule.mem_inf.2 ⟨hZ, h⟩)
  unfold BD at hB
  obtain ⟨v, hv⟩ := LinearMap.mem_range.1 hB
  rw [Submodule.mem_bot]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [Submodule.mem_comap]
  unfold coB1
  refine LinearMap.mem_range.2 ⟨Cd.u.symm v, ?_⟩
  funext g
  apply Cd.u.injective
  have hg := congrFun hv (eG g)
  rw [trC_apply_eG] at hg
  show Cd.u (uElt r χ (g : GG) • Cd.u.symm v - Cd.u.symm v) = Cd.u ((z : Dw → M) g)
  rw [← hg, map_sub, Cd.u_act, AddEquiv.apply_symm_apply]
  try rfl

theorem unr_exists (I' : Subgroup Dw) (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw))
    (h : (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ unrH1 (resRep (uRep O' (M := M) r χ) Dw) I') :
    ∃ m : M, ∀ g : Dw, g ∈ I' → (z : Dw → M) g = uElt r χ (g : GG) • m - m := by
  unfold unrH1 at h
  rw [LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap] at h
  unfold coB1 at h
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 h
  exact ⟨m, fun g hg => (congrFun hm ⟨g, hg⟩).symm⟩

variable {I : Subgroup G} {I' : Subgroup Dw}

include heG in

theorem hW_zero (hzero : divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L = divisibleCocycles Cd.Ce.L ⊓ (Z1urD Cd.Ce.L I ⊔ BD Cd.Ce.L))
    (hI' : ∀ h ∈ I, eG.symm h ∈ I')
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M))
    (h : (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈
      Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ unrH1 (resRep (uRep O' (M := M) r χ) Dw) I') :
    trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L := by
  obtain ⟨m, hm⟩ := unr_exists I' z (Submodule.mem_inf.1 h).2
  have hZ := trC_Z1D' Cd heG z hz
  have hU : trC Cd (z : Dw → M) ∈ Z1urD Cd.Ce.L I := by
    unfold Z1urD
    refine ⟨Cd.u m, fun g hg => ?_⟩
    show Cd.u ((z : Dw → M) (eG.symm g)) = actD Cd.Ce.L g (Cd.u m) - Cd.u m
    rw [hm _ (hI' g hg), map_sub, Cd.u_act, MulEquiv.apply_symm_apply]
  have hmem : trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ (Z1urD Cd.Ce.L I ⊔ BD Cd.Ce.L) :=
    Submodule.mem_inf.2 ⟨hZ, Submodule.mem_sup_left hU⟩
  rw [← hzero] at hmem
  exact (Submodule.mem_inf.1 hmem).2

include heG in

theorem hB_zero (hzero : divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L = divisibleCocycles Cd.Ce.L ⊓ (Z1urD Cd.Ce.L I ⊔ BD Cd.Ce.L))
    (hI : ∀ g : Dw, g ∈ I' → eG g ∈ I)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M))
    (h : trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L) :
    (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈
      Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ unrH1 (resRep (uRep O' (M := M) r χ) Dw) I' := by
  have hZ := trC_Z1D' Cd heG z hz
  have hmem : trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L := Submodule.mem_inf.2 ⟨hZ, h⟩
  rw [hzero] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (Submodule.mem_inf.1 hmem).2
  unfold Z1urD at ha
  obtain ⟨x, hx⟩ := ha
  unfold BD at hb
  obtain ⟨v, hv⟩ := LinearMap.mem_range.1 hb
  refine Submodule.mem_inf.2 ⟨Submodule.mem_map.2 ⟨z, hz, rfl⟩, ?_⟩
  unfold unrH1
  rw [LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]
  unfold coB1
  refine LinearMap.mem_range.2 ⟨Cd.u.symm (x + v), ?_⟩
  funext g
  apply Cd.u.injective
  have hg := congrFun hab (eG (g : Dw))
  rw [Pi.add_apply, trC_apply_eG, hx _ (hI _ g.2), ← hv] at hg
  show Cd.u (uElt r χ ((g : Dw) : GG) • Cd.u.symm (x + v) - Cd.u.symm (x + v)) = Cd.u ((z : Dw → M) g)
  rw [← hg, map_sub, Cd.u_act, AddEquiv.apply_symm_apply]
  show actD Cd.Ce.L (eG (g : Dw)) (x + v) - (x + v) =
    (actD Cd.Ce.L (eG (g : Dw)) x - x) + (actD Cd.Ce.L (eG (g : Dw)) v - v)
  rw [map_add]
  abel

end Conds

end Formalism.MainNotions.N.K.TBb

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Cyc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem cycW_of : CycW i dc := by
  intro w hw g
  have h1 := Formalism.MainNotions.N.KBKa.cycZ_eq_χQ (D.nbr i w hw) (D.loc (D.nd.l i)) (eW i dc hw g)
  have h2 := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw (eW i dc hw g)
  have h3 : ((Br.ι (D.nbr i w hw) (eW i dc hw g) : Dec (F := D.host.E) (D.nd.plOm.1 w)) : GE D.nd) = (g : GE D.nd) := by
    show (((D.nbr i w hw).e.symm ((D.nbr i w hw).e (MulEquiv.subgroupCongr (Dw_idx i dc hw) g)) :
      ↥(Dec (F := D.host.E) (D.nd.plOm.1 w))) : GE D.nd) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [h3] at h1
  show ((((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).χ (eW i dc hw g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) = _
  rw [h2, ← h1]
  rfl

theorem eW_inert' {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) (hh : h ∈ Br.inert D.nbr i w hw) :
    (eW i dc hw).symm h ∈ (Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w)) := by
  rw [Subgroup.mem_subgroupOf]
  have hA : Aw i dc (idx i dc w) = D.nd.plOm.1 w := by
    unfold Aw
    rw [plOf_idx i dc (mem_plSet i dc hw)]
  rw [hA]
  exact hh

end Cyc

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem sE_cont (c' : Fin D.R.t) :
    Continuous fun g : GE D.nd => sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) g := by
  have := D.nd.trO i
  have hc1 : Continuous fun g : GE D.nd => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
    have : (fun g : GE D.nd => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := funext fun g => by rw [map_inv]
    rw [this]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  have h := hc1.mul (D.nd.chi_cont i ((c' : ℕ) + 1))
  have he : (fun g : GE D.nd => sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) g) =
      fun g => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) :=
    funext fun g => (chi_ratio (i := i) c' g).symm
  rw [he]
  exact h

theorem epsL_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c' : Fin D.R.t) :
    Continuous fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^
      (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) := by
  have he : (fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^
      (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1)) = fun h => algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))
        ((D.nbr i w hw).eO (sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) (((eW i dc hw).symm h : Dw i dc (idx i dc w)) : GE D.nd))) := by
    funext h
    rw [eO_sE i dc (cycW_of i dc) hw, MulEquiv.apply_symm_apply, map_pow]
  rw [he]
  exact continuous_subtype_val.comp ((D.nbr i w hw).eO_cont.comp
    ((sE_cont i c').comp (continuous_subtype_val.comp (eW_symm_cont i dc hw))))

variable [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

set_option maxHeartbeats 1000000 in

theorem coefDict_of
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) :
    Nonempty (CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
      (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1)) := by
  obtain ⟨φ, hφ⟩ := blkTw_of_def hD hN c hc
  obtain ⟨c', rfl⟩ : ∃ c', Fin.succ c' = c := Fin.exists_succ_eq.mpr (by
    rintro rfl
    simp at hc)
  exact ⟨coefDictOf i dc Dd (cycW_of i dc) hw c'.succ φ hφ (epsL_cont i dc hw c')⟩

end Dict

section Len

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

set_option maxHeartbeats 1000000 in

theorem lenMap_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hwrow : w ∈ dc.row) (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ))
    (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
      (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1)) :
    LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB := by
  have hT := hTB w hw hwrow
  have het : (c : ℕ) - 1 < D.R.t := by
    have := c.2
    omega
  have h2 := trivial_bound_general hT het Cd.Ce
  have hp : (Br.PD D.loc D.nbr i w hw).p = D.nd.l i := Br.PD_p D.loc D.nbr i w hw
  refine lenMap_gen Cd (eW_symm_cont i dc hw) hp ?_ ?_
  · intro z hz hF
    unfold Fc at hF
    split_ifs at hF with h1
    · exact hW_zero Cd (eW_symm_cont i dc hw) (h2.2 (by omega)) (fun h hh => eW_inert' i dc hw h hh) z hz hF
    · exact hW_bot Cd z hz hF
  · intro z hz hH
    unfold Fc
    split_ifs with h1
    · exact hB_zero Cd (eW_symm_cont i dc hw) (h2.2 (by omega)) (eW_inert i dc hw) z hz hH
    · exact hB_bot Cd (eW_symm_cont i dc hw) (h2.1 (by omega)) z hz hH

end Len

section Dict2

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def YtPsi : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
      ∀ Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
          (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1),
        ∃ Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
            ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL),
          YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
          PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd

set_option maxHeartbeats 4000000 in

theorem tbDict2_of (cB : ℕ)
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hTB : TrivialBoundAtRows i dc r π cB)
    (hY : YtPsi i dc r π Dd) : TBDict2 i dc r π Dd cB := by
  intro w hw hwrow c hcc
  obtain ⟨Cd⟩ := coefDict_of i dc r ρ π g0 eB e₁ s Dd hD hN hw c hcc
  obtain ⟨Y, hY1, hY2⟩ := hY w hw hwrow c hcc Cd
  refine ⟨Y, Cd, hY1, hY2, ?_, ?_⟩
  · exact yLoc_of i dc r π g0 eB e₁ s Dd hD hc c (idx i dc w)
  · exact lenMap_of i dc r π Dd cB hTB hw hwrow c hcc Cd

theorem trivial_bound_target_of_psi (cB : ℕ)
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hTB : TrivialBoundAtRows i dc r π cB)
    (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i) (hY : YtPsi i dc r π Dd) : TBTarget i dc Dd cB :=
  trivial_bound_target_of_dict i dc r π Dd cB hTB hTie (tbDict2_of i dc r ρ π g0 eB e₁ s Dd cB hD hN hc hTB hY)

end Dict2

end Formalism.MainNotions.N.K.TBb

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)

theorem trivialBoundAtRows_of_admTB (cB : ℕ) (hG : SelfGood i) (h : Formalism.MainNotions.EmbeddingTypes.admTB i r π dc cB) : TrivialBoundAtRows i dc r π cB :=
  fun w hw hrow => h w hw hrow (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (hG w hw)

end Formalism.MainNotions.N.K.TB

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.StC

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf Formalism.MainNotions.N.K.TBa Formalism.MainNotions.N.KLift

section EmbRow

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))

theorem msW_apply {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i)
    (g : Br.G D.nbr i w hw) (a b : Fin D.R.nV) :
    MsW i r hw x g a b = eS i hw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (rTwO D.nd i r x ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) a b)) := by
  rw [msW_entry]
  first
  | rfl
  | simp [Matrix.map_apply]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem embRW_of {T : Subalgebra (D.nd.O i) (D.nd.X i → D.nd.O i)} {π : D.nd.X i} {ε : GE D.nd →* (D.nd.O i)ˣ}
    {g0 : GE D.nd} {eB e₁ s : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) T (Formalism.MainNotions.N.RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) ε g0 eB e₁ s Dd)
    [Module.Finite (D.nd.O i) Dd.R']
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) : EmbRW i dc r Dd hw := by
  obtain ⟨hr', hsm, hχ⟩ := ringDef_lift i r Dd hD
  have := nzsd_R' i Dd
  have : Module.Free (D.nd.O i) Dd.R' := Module.free_of_finite_type_torsion_free'
  set ρP := resRep (lRep (D.nd.O i) Dd.r Dd.χ) (Dw i dc (idx i dc w)) with hρP
  set e := eS i hw
  let κ : Dd.R' →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) :=
    (Dd.R').val.toLinearMap
  have hκ : Function.Injective κ := Subtype.val_injective
  let Λ := liftK (V := Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) κ
  have hΛs : ∀ m (s : nonZeroDivisors (D.nd.O i)), (s : D.nd.O i) • Λ (LocalizedModule.mk m s) = κ m := by
    intro m s
    rw [← map_smul, smul_mk, liftK_mkK]
  have hΛi : ∀ v, Λ v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h1 := hΛs m s
      rw [hv, smul_zero] at h1
      rw [hκ (h1.symm.trans (map_zero κ).symm), LocalizedModule.zero_mk]
  have hΛe : ∀ (γ : ↥(Dw i dc (idx i dc w))) v, Λ (locRep ρP γ v) =
      ((Formalism.NG.uElt Dd.r Dd.χ (γ : GE D.nd) : Dd.R') :
        Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * Λ v := by
    intro γ v
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h0 : locRep ρP γ (LocalizedModule.mk m s) = LocalizedModule.mk (ρP γ m) s := LocalizedModule.map_mk _ _ _ _
      rw [h0]
      apply smul_cancel s
      rw [hΛs, ← mul_smul_comm, hΛs]
      rfl
  let Ψ : Dd.X' × Fin D.R.nV → TrV e (MK (O := D.nd.O i) Dd.R') →ₗ[↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1]
      (Fin D.R.nV → ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1) := fun q =>
    { toFun := fun v a => e ((Λ (untr e v)) q.1 a q.2)
      map_add' := fun v v₂ => funext fun a => by
        show e ((Λ (untr e v + untr e v₂)) q.1 a q.2) = _
        rw [map_add]
        simp [map_add]
      map_smul' := fun c v => funext fun a => by
        show e ((Λ (e.symm c • untr e v)) q.1 a q.2) = c * e ((Λ (untr e v)) q.1 a q.2)
        rw [smulK]
        simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul] }
  haveI : FiniteDimensional (↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1) (TrV e (MK (O := D.nd.O i) Dd.R')) :=
    finDim_of_lat (Ow := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Qp := ℚ_[D.nd.l i])
      (latOf e (selfO i hw) mkK (eW i dc hw).symm.toMonoidHom (heS i hw) (locRep ρP) ρP mkK_inj
        (fun γ m => (locRep_mkK _ γ m).symm) mkK_span)
  have hinj : ∀ v, (∀ q, Ψ q v = 0) → v = 0 := by
    intro v hv
    have h0 : Λ (untr e v) = 0 := by
      funext x'
      ext a b
      have := congrFun (hv (x', b)) a
      simpa [Ψ] using this
    exact hΛi _ h0
  obtain ⟨m, xs, hxs⟩ := fin_sel Ψ hinj
  refine ⟨m, fun a => Dd.p (xs a).1, LinearMap.pi fun a => Ψ (xs a), fun v v' hvv => ?_, fun g v => funext fun a => ?_⟩
  · rw [← sub_eq_zero]
    refine hxs _ fun a => ?_
    rw [map_sub, sub_eq_zero]
    exact congrFun hvv a
  · have key : ∀ (q : Dd.X' × Fin D.R.nV) (γ : ↥(Dw i dc (idx i dc w))),
        (γ : GE D.nd) = ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) → ∀ b,
        e ((Λ (locRep ρP γ (untr e v))) q.1 b q.2) = (MsW i r hw (Dd.p q.1) g).mulVec (Ψ q v) b := by
      intro q γ hγ b
      rw [hΛe, Pi.mul_apply, hγ, uElt_at i r Dd hr' hsm hχ, Matrix.mul_apply, map_sum]
      simp only [Matrix.mulVec, dotProduct, msW_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [Ψ, Matrix.map_apply, map_mul]
      exact Or.inl rfl
    funext b
    exact key (xs a) ((eW i dc hw).symm g) rfl b

end EmbRow

end Formalism.MainNotions.N.K.StC

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StC

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Clauses

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (cB : ℕ)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def ClauseTB : Prop :=
  ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → ∀ w ∈ rowsN i dc,
      (∀ ψ : Ymod Dd.r Dd.χ Dd.E →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c,
        (∀ g ∈ (decs D.host.E (Aw i dc)) w, ∀ y, ψ (uElt Dd.r Dd.χ g • y) = uElt Dd.r Dd.χ g • ψ y) →
        ∀ z : coZ1s (QS.resU i dc Dd c w),
          (∀ g : (decs D.host.E (Aw i dc)) w, (z : (decs D.host.E (Aw i dc)) w → blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) g =
            ψ (yY Dd.r Dd.χ Dd.E (g : GE D.nd))) →
          (((D.nd.l i : ℕ) : D.nd.O i) ^ cB) • (Submodule.mkQ _ z : H1z (QS.resU i dc Dd c w)) ∈
            St.FS i r π dc g0 eB e₁ s Dd hD hc c w) ∧
      Module.length (D.nd.O i) (↥(lcH1 (QS.resU i dc Dd c w) ⊓
          divBy (St.FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
        (St.FS i r π dc g0 eB e₁ s Dd hD hc c w).comap (lcH1 (QS.resU i dc Dd c w) ⊓
          divBy (St.FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype) ≤
        eON i * (cB : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 1)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def ClauseChi : Prop :=
  ∀ c : Fin (D.R.t + 1), 2 ≤ (c : ℕ) →
    InChiFixReal (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ Dd.E (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
      (qsN i dc) (ShaN i ((c : ℕ) - 1)) (St.FS i r π dc g0 eB e₁ s Dd hD hc c) (QS.Io i) (QS.IS i) (QS.I i dc)
      (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def ClauseLoc1 : Prop :=
  InChiLoc (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk QS.c1) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc)
    (St.FS i r π dc g0 eB e₁ s Dd hD hc QS.c1) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd)
    (QS.ζO i dc) (QS.nQ i dc)

end Clauses

section Proofs

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (cB : ℕ)

theorem locPos (hE : QS.Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r)
    (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (hQP : QS.QPow i)
    (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) : QS.LocClause i dc Dd c := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr hc0
  apply QS.locClause (dc := dc) (hE := hE) (hN := hN) (hG4 := hG4) (hdec := hdec) (hG5 := hG5) (h5x := h5x)
    (hQP := hQP) (c' := c') (hS := QS.locS (hE := hE) (hN := hN) (hG5 := hG5) (h5x := h5x) (c' := c'))

theorem FS_eq (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) :
    St.FS i r π dc g0 eB e₁ s Dd hD hc c = QS.Fpos i dc Dd c := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr hc0
  funext w
  rfl

theorem first_character_index_ne_zero : (QS.c1 (D := D)) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  simp [QS.c1] at h'

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem first_local_clause_of (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (hQP : QS.QPow i) :
    ClauseLoc1 i r π dc g0 eB e₁ s Dd hD hc := by
  have hE := QS.ev_of (hD := hD)
  unfold ClauseLoc1
  rw [FS_eq (dc := dc) (hD := hD) (hc := hc) (c := QS.c1) (hc0 := first_character_index_ne_zero)]
  exact locPos (dc := dc) (hE := hE) (hN := hN) (hG4 := hG4) (hdec := hdec) (hG5 := hG5) (h5x := h5x)
    (hQP := hQP) (c := QS.c1) (hc0 := first_character_index_ne_zero)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem chi_of (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (hQP : QS.QPow i) :
    ClauseChi i r π dc g0 eB e₁ s Dd hD hc := by
  have hE := QS.ev_of (hD := hD)
  unfold ClauseChi
  intro c hc2
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc2
  refine And.intro ?_ ?_
  · rw [FS_eq (dc := dc) (hD := hD) (hc := hc) (c := c) (hc0 := hc0)]
    exact locPos (dc := dc) (hE := hE) (hN := hN) (hG4 := hG4) (hdec := hdec) (hG5 := hG5) (h5x := h5x)
      (hQP := hQP) (c := c) (hc0 := hc0)
  · exact ShaT.tieSel2_full (dc := dc) (hD := hD) (hN := hN) (F0 := St.FirstBlockLocalConditions i r π dc g0 eB e₁ s Dd hD hc)
      (c := c) (hc := hc2)

omit [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem FS_row (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) {w : ℕ} (hw : w ∈ rowsN i dc) :
    St.FS i r π dc g0 eB e₁ s Dd hD hc c w = TB.Fc i dc Dd c w := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr hc0
  show QS.Fpos i dc Dd c'.succ w = TB.Fc i dc Dd c'.succ w
  rw [QS.Fpos_row (Dd := Dd) (c := c'.succ) (hw := hw)]
  rfl

omit [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem tb_of_target (hT : TB.TBTarget i dc Dd cB) : ClauseTB i r π dc g0 eB e₁ s Dd hD hc cB := by
  intro c hc1 w hw
  have hc0 : c ≠ 0 := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_zero] at this
    omega
  have hF : St.FS i r π dc g0 eB e₁ s Dd hD hc c w = TB.Fc i dc Dd c w :=
    FS_row i r π dc g0 eB e₁ s Dd hD hc c hc0 hw
  have hx := hT w hw c hc1
  rewrite [← hF] at hx
  exact ⟨hx.2.2.1, hx.2.2.2⟩

end Proofs

section ForRN

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π)) (cB : ℕ)

end ForRN

end Formalism.MainNotions.N.K.StC

end
end
