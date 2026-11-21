import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeoHalfMove
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesBaseTwistedUniversalRational
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyExtAnd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTransformCuspFormsReadsCosetSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSeriesCoeffBoundedInSupOfTwistSeriesSid

section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def rhoEquiv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) : M ≃ₗ[K] M :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rho_rho {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g g' : G) (x : M) :
    ρ g (ρ g' x) = ρ (g * g') x := by rw [map_mul]; rfl

theorem rho_inv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) (x : M) :
    ρ g (ρ g⁻¹ x) = x := by rw [rho_rho, mul_inv_cancel, map_one]; rfl

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ)

abbrev realDatMovedReadingsKeepScalars : RealDat3 D A3 Ks := ⟨moveR Rl.toRealDat w, Rl.plI, Rl.SF, Rl.phs, Rl.lam3⟩

variable (kap : ℝ) (lam : type_of% Rl.lam3)

abbrev fullHeckeRealDatMovedReadings : RealDat3 D A3 Ks := (realDatMovedReadingsKeepScalars Rl w).updS kap lam

variable {Rl w kap lam}

set_option maxHeartbeats 4000000 in

theorem heckeCharacterisation_transfer_movedReadings {F : Face3 D A3} (h : Rl.Char3 F) (hs : (fullHeckeRealDatMovedReadings Rl w kap lam).IsScal F) : (fullHeckeRealDatMovedReadings Rl w kap lam).Char3 F := by
  obtain ⟨h1, h2, h5, hi, h6, h7, h8, f1, f2, f3, -, ht, hp, ha⟩ := h
  refine ⟨h1, ⟨h2.1, h2.2, h2.3, h2.4, h2.5⟩, ?_, ⟨hi.1, hi.2, hi.3, hi.4, hi.5⟩, ?_, ?_, ?_, f1, f2, f3, hs,
    ⟨ht.1, ht.2, ht.3, ht.4, ht.5⟩, fun i => ⟨(hp i).1, fun hc x => ?_⟩, ha⟩
  · exact ⟨h5.1, h5.2, h5.3, h5.4, h5.5, h5.6, h5.7, h5.8⟩
  · exact ⟨h6.1, h6.2, h6.3, h6.4, h6.5, h6.6, h6.7, h6.8, h6.9, h6.10, h6.11, h6.12, h6.13, h6.14, h6.15, h6.16, h6.17,
      h6.18, h6.19, h6.20, h6.21⟩
  · exact ⟨h7.1, h7.2, h7.3, h7.4, h7.5, h7.6, h7.7, h7.8, h7.9, h7.10, h7.11⟩
  · exact ⟨h8.1, h8.2, h8.3, h8.4, h8.5, h8.6, h8.7⟩
  · obtain ⟨c, hc1, hc2⟩ := hc
    obtain ⟨y, hy⟩ := (hp i).2 ⟨c, hc1, fun x => (hc2 x).elim fun y hy => ⟨(Rl.FW i).ρ (w i (sg0 D A3.A)) y, hy⟩⟩ x
    exact ⟨(Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ y, (congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ y)).trans hy⟩

variable {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (w)

abbrev moveS : NX.RatDat D.ntw :=
  { S with
    A := fun n => moveForms (S.A n) fun σ =>
      (YS.fi (NX.idxOf D n)).eG.symm (w (NX.idxOf D n) σ * (w (NX.idxOf D n) (sg0 D A3.A))⁻¹) }

variable {w} (kap lam) (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)

def moveIso (i : Fin D.R.m) : NX.FormsIso ((moveS w YS).A ((i : ℕ) + 1)) ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i) where
  eK := (YS.fi i).eK
  eK_LL := (YS.fi i).eK_LL
  e := (YS.fi i).e.trans (rhoEquiv (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹)
  eG := (YS.fi i).eG
  eW := (YS.fi i).eW
  wk x := ((YS.fi i).wk x).trans ⟨(hst i _ _).1, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).1 h⟩
  mkK x := ((YS.fi i).mkK x).trans ⟨(hst i _ _).2, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).2 h⟩
  rho g x := by
    change (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e ((S.A _).ρ g x)) =
      (Rl.FW i).ρ ((YS.fi i).eG g) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))
    rw [(YS.fi i).rho, rho_rho, rho_rho, Subgroup.mem_center_iff.1 (inv_mem (hw i _))]
  chi := (YS.fi i).chi
  j σ x := by
    change (Rl.FW i).j σ ((Rl.FW i).ρ (w i σ) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))) =
      (YS.fi i).eW σ ((S.A _).j σ ((S.A _).ρ ((YS.fi (NX.idxOf D ((i : ℕ) + 1))).eG.symm
        (w (NX.idxOf D ((i : ℕ) + 1)) σ * (w (NX.idxOf D ((i : ℕ) + 1)) (sg0 D A3.A))⁻¹)) x))
    rw [NX.idxOf_succ, ← (YS.fi i).j, (YS.fi i).rho, MulEquiv.apply_symm_apply, rho_rho]

def moveYS : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) where
  fi := moveIso kap lam YS hw hst
  geq := YS.geq
  rho := YS.rho
  chi := YS.chi
  eF := YS.eF
  bsup := YS.bsup
  act := YS.act

theorem j_moveYS (i : Fin D.R.m) (x : S.WL ((i : ℕ) + 1)) :
    ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i).j (sg0 D A3.A) (((moveYS kap lam YS hw hst).fi i).e x) =
      (Rl.FW i).j (sg0 D A3.A) ((YS.fi i).e x) :=
  congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ _)

def moveH (H : NX.NExpRealH Rl cG S YS) : NX.NExpRealH (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) where
  hL := H.hL
  hs := H.hs
  cHk := H.cHk
  cHk_zero := H.cHk_zero
  cHk_unit := H.cHk_unit
  cHk_pow := H.cHk_pow
  hkEq := H.hkEq

theorem reads_move {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} (h : GlobalTheory.ExportPin.Reads Rl cG S YS hL) :
    GlobalTheory.ExportPin.Reads (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) hL := by
  intro i k P h1 h2 h3 α R h4 h5 x
  rw [j_moveYS, j_moveYS]
  exact h i k P h1 h2 h3 α R h4 h5 x

variable (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem realRd_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ) :
    realRd (moveYS kap lam YS hw hst) v₀ hρ i j b ν = realRd YS v₀ hρ i j b ν := by
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      evK (moveYS kap lam YS hw hst) v₀ hρ i j b x = evK YS v₀ hρ i j b x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
    | tmul a f =>
      exact congrArg (fun y => ρ.e i b a • (Rl.HW j (sg0 D A3.A)).e y (v₀ j _)) (j_moveYS kap lam YS hw hst j (Subtype.val f))
  exact LinearMap.ext fun f => congrArg (ν⁻¹ • ·) (key _)

theorem ratRow_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) :
    RatRow (moveYS kap lam YS hw hst) v₀ hρ i j b ↔ RatRow YS v₀ hρ i j b :=
  exists_congr fun ν => and_congr Iff.rfl (by rw [realRd_move])

variable {YS v₀}

theorem rd_move (Z : ExportTie YS v₀) :
    (fun i j b => realRd (moveYS kap lam YS hw hst) v₀ Z.good i j b (Z.ν i j b) : Rds D.nexp Z.ρ) = Z.rd :=
  funext fun i => funext fun j => funext fun b => realRd_move kap lam YS hw hst v₀ Z.good i j b _

end GlobalTheory.Unframe

end
end

section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ} (kap : ℝ) (lam : type_of% Rl.lam3)
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem pin_move {ρ : Setup D.ntw} (h : RealPin Rl cG ρ) : RealPin (fullHeckeRealDatMovedReadings Rl w kap lam) cG ρ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16, h.17, h.18⟩

theorem isNorm_move {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (ν : ℂ) :
    IsNorm (fullHeckeRealDatMovedReadings Rl w kap lam) v₀ B ν ↔ IsNorm Rl v₀ B ν := Iff.rfl

theorem vec_move {j : Fin D.R.m} (h : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) :
    FWT.IsChosenExtremalVector (fullHeckeRealDatMovedReadings Rl w kap lam).toRealDat j (sg0 D A3.A) (v₀ j _) := h

theorem isScalar_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {ν : ℂ}
    (h : IsScalar YS v₀ hρ i j b ν) : IsScalar (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ hρ i j b ν :=
  ⟨h.ne, fun h' => (isNorm_move kap lam _ _).2 (h.norm (h'.imp fun _ => (isNorm_move kap lam _ _).1)), fun h' =>
    (congrArg (Rat hρ) (realRd_move kap lam YS hw hst v₀ hρ i j b ν)).mpr
      (h.rat ((ratRow_move kap lam YS hw hst v₀ hρ i j b).1 h'))⟩

def moveZ (Z : ExportTie YS v₀) : ExportTie (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ where
  ρ := Z.ρ
  good := Z.good
  pin := pin_move kap lam Z.pin
  vec := fun j => vec_move kap lam (Z.vec j)
  ν := Z.ν
  scalar := fun i j b => isScalar_move kap lam hw hst Z.good i j b (Z.scalar i j b)
  tie := cast (congrArg (Comparison₂ Z.good (Y := D.nexp)) (rd_move kap lam hw hst Z).symm) Z.tie
  hecke := fun i j b => (congrArg HeckeTie (realRd_move kap lam YS hw hst v₀ Z.good i j b _)).mpr (Z.hecke i j b)
  univ := Z.univ


end GlobalTheory.Unframe

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatBundles

theorem ratHyp {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (hF : FieldOk X)
    (hP : ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (j : Fin D.R.m) : GlobalTheory.BigOn.Exp.RatHyp X.core X.R X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O i j (X.space_eq j) :=
  have hC := X.char
  { size := X.size
    host := X.host
    std := X.std j
    laws := X.geo.fw.laws
    core := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩
    unif := X.unif
    fw := ⟨X.geo.fw⟩
    tieIn := ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
    io := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
    guard := X.guard
    fin := X.finT
    pins := X.geo.pins j
    phase := by
      convert X.geo.phase j X.unif using 2
      rename_i k
      rw [X.phs k]
      simp
    frame := hP j _
    galois := hF.galois
    small := ⟨hF.vals, hF.ray, hF.roots⟩
    inUse := hi
    low := Y.low i }

theorem levelOf {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) : Y.Z.ρ.LevelOf D.nexp :=
  ⟨fun i j b => (Y.Z.tie i j b).U_eq, fun i j b => (Y.Z.tie i j b).psiU_eq⟩

theorem rat_of_split (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hS : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat) {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D}
    (Y : SerSide X E) (hF : FieldOk X) (hsp : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK)
    (hP : ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (j : Fin D.R.m) (b : Bool) : RatRow Y.YS X.geo.v₀ Y.Z.good i j b :=
  GlobalTheory.T.thetaSeries_base_twisted_universal_rational hA hA.rayClassFieldSt (GlobalTheory.SerStd.seriesRatS_of hS) D X.Γ X.Pl0 X.I0 X.T X.A3 X.core X.R X.cG Y.S Y.YS
    X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O Y.Z.ρ Y.Z.good i j b (X.space_eq j) Y.Z.pin (levelOf Y) hsp (ratHyp X Y hF hP hi j)

theorem rat_bundles : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b :=
  fun hA hS _ X _ Y hF hP _ hi j b => rat_of_split hA hS X Y hF hF.split hP hi j b

end GlobalTheory.RatBundles
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_thetaSeries_of_twistSeriesSideData : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b := by
  atlas_forward_decl GlobalTheory.RatBundles.rat_bundles
end

section
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

open GlobalTheory.TwInputs GlobalTheory.RealGeo Formalism.L2.Pj Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

set_option maxHeartbeats 8000000 in

theorem exists_framed (hP : GlobalTheory.Published.CuspRapidDecay) (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (hF : FieldOk X) :
    ∃ (X' : RealSide D) (Y' : SerSide X' E), FieldOk X' ∧
      (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X'.core X'.R.toRealDat j X'.core.σ₀ hV) ∧
      (∀ i j b, RatRow Y'.YS X'.geo.v₀ Y'.Z.good i j b → RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧
      (XiBdd Y'.Z.rd → XiBdd Y.Z.rd) := by
  have hC : GlobalTheory.Core5 X.R.toRealDat X.F.lv2 := ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.thP⟩
  obtain ⟨c', w, hw, hfr, B, hB⟩ := exists_framed_half hP X.size hC X.geo X.unif X.inGeo
  obtain ⟨kap, lam, hs⟩ := scalars_exist (F := X.F) (realDatMovedReadingsKeepScalars X.R w)
  have hch : (fullHeckeRealDatMovedReadings X.R w kap lam).Char3 X.F := heckeCharacterisation_transfer_movedReadings X.char hs
  obtain ⟨B', -, hB', -⟩ := @geoHalf_upd D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (moveR X.R.toRealDat w) _ kap X.R.lam
    X.R.err0 B
  obtain ⟨κ, v₀, fw, bar, O, pins, rho, eqa, ct, phase⟩ := B'
  obtain rfl : v₀ = X.geo.v₀ := (eq_of_heq hB').trans hB
  let g : @GeoHalf D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat fun _ => 1 :=
    @GeoHalf.mk D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat _
      κ X.geo.v₀ fw bar O pins rho eqa ct phase
  have hpb : X.core.pb = X.R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs X.core.toCore X.R.toRealDat X.geo.fw.laws.toLawsM hC.lev
      ((X.geo.pins ⟨0, by have := D.R.two_le_m; omega⟩).2.tuple ()).half
  obtain ⟨hI, hU, hInt⟩ := @GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral hP D X.Γ _ _ X.Pl0 X.T X.A3.A (setCE X.core c') X.alg
    (fullHeckeRealDatMovedReadings X.R w kap lam).toRealDat _ g
    ⟨hch.lev, hch.grp.red_R, hch.grp.red_L, hch.grp.record, hch.fam, hch.models, hch.chain, hch.thP⟩ hch.grp.chiW hpb X.size
  have hst : ∀ i, (X.R.FW i).MKStable := fun i => (X.integral i).2.2
  let X' : RealSide D := @RealSide.mk D X.Γ X.grp X.fin X.Pl0 X.I0 X.T X.A3 (setCE X.core c') X.alg (fullHeckeRealDatMovedReadings X.R w kap lam) X.F X.cG g
    hch X.phs X.guard X.valKs X.idem hU hInt hI X.finT X.host X.std X.size
  let Y' : SerSide X' E :=
    { S := moveS w Y.YS
      YS := moveYS kap lam Y.YS hw hst
      sup := Y.sup
      H := moveH kap lam Y.YS hw hst Y.H
      reads := reads_move kap lam Y.YS hw hst Y.reads
      del := Y.del
      Z := moveZ kap lam hw hst Y.Z
      U_eq := Y.U_eq
      psi_eq := Y.psi_eq
      low := Y.low
      Sb := Y.Sb
      B_range := Y.B_range
      hk_emb := Y.hk_emb
      hk_split := Y.hk_split
      off := Y.off
      all := Y.all }
  refine ⟨X', Y', ⟨hF.galois, hF.star, hF.vals, hF.ray, hF.roots, hF.split⟩, hfr,
    fun i j b => (ratRow_move kap lam Y.YS hw hst X.geo.v₀ Y.Z.good i j b).1, fun h => ?_⟩
  rw [← rd_move kap lam hw hst Y.Z]
  exact h

end GlobalTheory.Unframe

section

open GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf

theorem GlobalTheory.Unframe.rat_and_xiBdd : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧ XiBdd Y.Z.rd := by
  intro hP hA hR hS D X E Y hF
  obtain ⟨X', Y', hF', hfr, h1, h2⟩ := GlobalTheory.Unframe.exists_framed hP X Y hF
  exact ⟨fun i hi j b => h1 i j b (GlobalTheory.T.exists_rational_thetaSeries_of_twistSeriesSideData hA hR D X' E Y' hF' hfr i hi j b), h2 (GlobalTheory.T.universalSeriesCoeff_boundedInSup_of_twistSeriesSideData hA hR hS D X' E Y' hF' hfr)⟩

end
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_rationality_and_coefficientBound : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) ∧ XiBdd Y.Z.rd := by
  atlas_forward_decl GlobalTheory.Unframe.rat_and_xiBdd
end
