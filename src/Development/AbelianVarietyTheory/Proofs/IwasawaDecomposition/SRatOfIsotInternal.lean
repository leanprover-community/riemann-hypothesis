import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaConjUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCAtState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelCharacterEqProdSuperdiagonalSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHeckeAtZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterPsiConditionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigSpanOfIsotInternal

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.RatDatRExp

theorem chi_val_small {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hL : R.toLevCh.Is A.μ0) (hV : GlobalTheory.RealGeo.ValKs R) (i : Fin D.R.m) (PP : Pl D.host.E) (hP : PP ∈ R.Pg)
    (u : (kP PP)ˣ) :
    ∃ y : Ks, ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) = D.what₂.embLL (algebraMap Ks D.what₂.LL y) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP PP)
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.coe_eq_zero_iff.mp h
    apply u.ne_zero
    rw [← ha, h0, map_zero]
  let k : D.host.Eˣ := Units.mk0 _ ha0
  obtain ⟨ι, hι, hint, happ⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι hι hint happ PP
  have hv : PP.valuation D.host.E (k : D.host.E) ≤ 1 := PP.valuation_le_one a
  have hinf := (GlobalTheory.UnramCharUnique.loc_parts he _ hv).1
  obtain ⟨y, hy⟩ := hV i (Formalism.L2.JoinChr.locU he.1 k) hinf
  have h1 := (hL.mu0 i).2 PP e he k (Formalism.L2.JoinChr.locU he.1 k) rfl
  have h2 := hL.chi i PP hP a k u rfl ha.symm
  refine ⟨y⁻¹, ?_⟩
  rw [MonoidHom.inv_apply] at h2
  have h3 : R.chi ((i : ℕ) + 1) PP u = ((R.C.mu0 i).locK PP k)⁻¹ := by rw [← h2, inv_inv]
  rw [h3, Units.val_inv_eq_inv_val, ← h1, hy, map_inv₀, map_inv₀]

end GlobalTheory.Mem.RatDatRExp

namespace GlobalTheory.Mem.RatDatRExp

theorem rhoStab_chiInLL0 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (kKs : C.Q.c.F →+* ↥D.LL0) (hk : ∀ x, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap C.Q.c.F D.what₂.LL x), Pins R F cG → GlobalTheory.RealGeo.InGeo g → ∀ j, 1 ≤ j → j ≤ D.R.m → NX.RhoStab (NX.ratDatR R cG kKs hk) j ∧ NX.ChiInLL0 (NX.ratDatR R cG kKs hk) j := by
  intro D G _ _ Pl0 I0 T A3 C _ R F cG B kKs hk hP _ j _ _
  refine ⟨?_, ?_⟩
  · intro g0 x hx
    change (R.FW (NX.idxOf D j)).ρ g0 x ∈ (R.FW (NX.idxOf D j)).WK
    change x ∈ (R.FW (NX.idxOf D j)).WK at hx
    by_cases hK : Formalism.IndefR.FWT.ActKeeps (κ := B.κ) B.O (NX.idxOf D j)
    · obtain ⟨hf, heq⟩ := (B.rhoGeo (NX.idxOf D j)).1 hK g0 ((B.fw.e (NX.idxOf D j)).symm ⟨x, hx⟩)
      rw [LinearEquiv.apply_symm_apply] at heq
      rw [← heq]
      exact Submodule.coe_mem _
    · rw [(B.rhoGeo (NX.idxOf D j)).2 hK g0]
      exact hx
  · intro g0
    change (((R.FW (NX.idxOf D j)).chi g0 : D.what₂.LLˣ) : D.what₂.LL) ∈ D.LL0
    have hL := hP.char.base.lev
    have hW := hP.char.base.grp.chiW
    have hV := hP.keep.valKs
    have hy : ∀ PP : R.Pg, ∃ y : C.Q.c.F,
        ((R.chi ((NX.idxOf D j : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g0 PP)) : ℂˣ) : ℂ) =
          D.what₂.embLL (algebraMap C.Q.c.F D.what₂.LL y) := fun PP =>
      chi_val_small R.toRealDat hL hV (NX.idxOf D j) PP.1 PP.2 _
    choose y hy using hy
    have h1 := hW (NX.idxOf D j) g0
    rw [Finset.prod_congr rfl (fun PP _ => hy PP), ← map_prod, ← map_prod] at h1
    have h2 := D.what₂.embLL.injective h1
    rw [h2, ← hk]
    exact (kKs _).2

end GlobalTheory.Mem.RatDatRExp
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
  GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.RatSide

theorem sRat_of_isotInternal : PrN → SerN → (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) →
    ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SRat hL := by
  intro hp hs hi hL
  have A := StepW.and (formsC_at_state hL) (StepW.and (GlobalTheory.HeightCounting.ThetaSt.main hL)
    (StepW.and (GlobalTheory.HeightCounting.RatSide.HeckeAtState.heckeAtState hL hp.decay hs.hkTr hs.hkRead)
    (StepW.and (GlobalTheory.T.level_character_psi_condition hL hp.decay hs.hkInt hs.hkTr hs.hkRead) (eig_span_of_isotInternal hp hi hL))))
  refine StepW.trans A (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx
  obtain ⟨hF, hθ, hH, hI, hE⟩ := H
  obtain ⟨θ, θne, hlp⟩ := hθ P x hx
  obtain ⟨hL', hst, h0, hrd⟩ := hH P x hx
  obtain ⟨eig, hea, hsp⟩ := hE P x hx θ hL' θne hlp hst h0 hrd
  have hint := hI P x hx θ hL' hlp hst hrd
  have hrc := GlobalTheory.Mem.RatDatRExp.rhoStab_chiInLL0 (Dof x) _ _ _ _ _ x.m.z.core x.m.z.R x.m.z.F x.m.z.cG x.m.z.geo (kKsOf x)
    (hkOf x) x.m.z.pins x.m.inGeo
  exact ⟨⟨kKsOf x, hkOf x,
    { Sb := SbD (Dof x)
      rho := fun j a b => (hrc j a b).1
      chi := fun j a b => (hrc j a b).2
      ks := fun j a b => (hF P x hx j a b).1
      fd := fun j a b => (hF P x hx j a b).2.1
      mk_fg := fun j a b => (hF P x hx j a b).2.2
      hL := hL'
      hs := hst
      hL_zero := h0
      θ := θ
      θ_ne := θne
      eig := eig
      span := hsp
      hL_int := hint },
    { hecke := hrd
      eig := hea
      Sb_le := overSet_SbD _
      lvl := hlp.1
      psi := hlp.2 }⟩⟩

theorem sRat_of_duties : GlobalTheory.Published.DiscreteSeriesUpqUnique → PrN → SerN →
    (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) →
    ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SRat hL :=
  fun _ => sRat_of_isotInternal

end GlobalTheory.HeightCounting.RatSide

end
end
