import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigSpanOfIsotInternal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigAdOfRowEig
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StableHeckeLevelCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StableHeckeLevelCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLineIffEigenSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLineIffEigenSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenSpanInclusionInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenSpanInclusionInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeDataSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeDataSplitPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionHoldsAllStages

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.RatSide
theorem eigAd_of_rowEig_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, (∀ (i : Fin (Dof x).R.m) (σ : (Dof x).what₂.FT) (k : ℕ) (Pl : PlE (Dof x).host) α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr → (Dof x).nd.goodRow σ → (Dof x).what₂.isot (i.1 + 1) σ ≠ ⊥ → (Dof x).what₂.embLL (eig (i.1 + 1) σ k Pl : (Dof x).what₂.LL) = hkNorm x.m.z.R i k Pl * GlobalTheory.EigRows.rowEig x.r.Y i σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k)) → EigAd x.r.Y (SbD (Dof x)) eig := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ eig heig => ?_
  intro i σ k Pl α Rr hd hσ y hy
  by_cases h0 : (Dof x).what₂.isot (i.1 + 1) σ = ⊥
  · rw [h0, Submodule.mem_bot] at hy
    subst hy
    simp
  · have e1 := heig i σ k Pl α Rr hd hσ h0
    have hP := (GlobalTheory.TwInputs.Eig.low_SbD (Dof x)).offPg x.m.z.lev.is hd.offS
    have e2 := GlobalTheory.EigRows.heckeOn_partR x.r.Y x.m.z.lev.is i hP hd.le hd.elt hd.reps σ
      ((GlobalTheory.EigRows.mem_isot_iff x.r.Y i σ y).1 hy)
    change hkNorm x.m.z.R i k Pl • Mult.heckeOn _ Rr (GlobalTheory.EigRows.readW x.r.Y i y) = _ • GlobalTheory.EigRows.readW x.r.Y i y
    rw [e2, e1, smul_smul]
end GlobalTheory.HeightCounting.RatSide
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.RatSide
theorem exists_eigAd_of_state_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∃ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig := by
  intro hL
  refine (StepW.and (_root_.GlobalTheory.HeightCounting.RatSide.eigAd_of_rowEig_alt hL) GlobalTheory.HeckeField.Gap.rowEig_mem_fixedField).trans (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx hL' h3 h5
  classical
  refine ⟨fun j σ k Pl => if h : ∃ c : ↥(Dof x).LL0, (Dof x).what₂.embLL (c : (Dof x).what₂.LL) =
      hkNorm x.m.z.R (idxOf (Dof x) j) k Pl *
        GlobalTheory.EigRows.rowEig x.r.Y (idxOf (Dof x) j) σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k) then h.choose else 0,
    H.1 P x hx _ ?_⟩
  intro i σ k Pl α Rr hk hg h0
  have t2 := H.2 P x hL' h3 h5 i σ k Pl α Rr hk h0
  have hI := congrArg (fun i' : Fin (Dof x).R.m => hkNorm x.m.z.R i' k Pl *
      GlobalTheory.EigRows.rowEig x.r.Y i' σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k)) (NX.idxOf_succ (Dof x) i)
  have hex : ∃ c : ↥(Dof x).LL0, (Dof x).what₂.embLL (c : (Dof x).what₂.LL) =
      hkNorm x.m.z.R (idxOf (Dof x) (i.1 + 1)) k Pl *
        GlobalTheory.EigRows.rowEig x.r.Y (idxOf (Dof x) (i.1 + 1)) σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k) :=
    let ⟨c, hc⟩ := t2; ⟨c, hc.trans hI.symm⟩
  refine Eq.trans ?_ (hex.choose_spec.trans hI)
  simp only [dif_pos hex]
end GlobalTheory.HeightCounting.RatSide
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.EigSpanTie
section Core
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Core
set_option maxHeartbeats 4000000 in
theorem mem_goodL_iff_iotaR_mem_goodW_of_level_psi : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x →
    ∀ θ : (∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ), (∀ kk, θ kk ≠ 1) →
      LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → ∀ j, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v : (SOf x).WL j,
        (v ∈ goodL (Dof x) (SOf x) θ j ↔
          GlobalTheory.EigSpanDesc.iotaR x.m.z.R (idxOf (Dof x) j) v ∈
            GlobalTheory.EigRows.goodW x.m.z.R.toRealDat x.m.z.F.lv2 (idxOf (Dof x) j)) := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x _ θ _ hlv j _ _ v
  obtain ⟨_, _, -, hidem, -, -⟩ := x.m.z.pins.keep.grp
  exact mem_goodL_iff_iotaR x.m.z.R x.m.z.F x.m.z.cG (kKsOf x) (hkOf x) θ x.m.intersectionNumber_baseChange.prim.unif
    x.m.z.pins.char.base.models.HW hidem hlv j v
end GlobalTheory.EigSpanTie
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_goodL_iff_iotaR_mem_goodW : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ θ : (∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ), (∀ kk, θ kk ≠ 1) → LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → ∀ j, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v : (SOf x).WL j, (v ∈ goodL (Dof x) (SOf x) θ j ↔ GlobalTheory.EigSpanDesc.iotaR x.m.z.R (idxOf (Dof x) j) v ∈ GlobalTheory.EigRows.goodW x.m.z.R.toRealDat x.m.z.F.lv2 (idxOf (Dof x) j)) := by
  atlas_forward_decl _root_.GlobalTheory.EigSpanTie.mem_goodL_iff_iotaR_mem_goodW_of_level_psi
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.EigSpanDesc
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Gen
theorem iotaR_injective_states_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ i : Fin (Dof x).R.m, Function.Injective (GlobalTheory.EigSpanDesc.iotaR x.m.z.R i) := by
  intro hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x _ i
  exact iotaR_injective_of x.m.z.R x.m.z.pins.char.base.models x.m.intersectionNumber_baseChange.prim.unif i
end GlobalTheory.EigSpanDesc
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iotaR_injective_at_level_a : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ i : Fin (Dof x).R.m, Function.Injective (GlobalTheory.EigSpanDesc.iotaR x.m.z.R i) := by
  atlas_forward_decl _root_.GlobalTheory.EigSpanDesc.iotaR_injective_states_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeckeDataAtState
theorem exists_hkDat_at_state_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x →
    ∀ (i : Fin (Dof x).R.m) (k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ k → k ≤ (Dof x).R.r → IsSplitPl (Dof x).host Pl →
      Pl ∉ SbD (Dof x) → ∃ α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ i k Pl _ hk hs hP => ?_
  obtain ⟨α, Rr, h, -⟩ := GlobalTheory.TwInputs.Eig.exists_hkDat (R := x.m.z.R) x.m.z.F x.m.z.pins.char.base.lev (subset_refl _)
    (GlobalTheory.TwInputs.Eig.low_SbD (Dof x)) i hs hP hk
  exact ⟨α, Rr, h⟩
end GlobalTheory.HeckeDataAtState
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hkDat_at_split_place : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (i : Fin (Dof x).R.m) (k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ k → k ≤ (Dof x).R.r → IsSplitPl (Dof x).host Pl → Pl ∉ SbD (Dof x) → ∃ α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr := by
  atlas_forward_decl _root_.GlobalTheory.HeckeDataAtState.exists_hkDat_at_state_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.EigSpanDesc
section Core
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Core
theorem spanC_of_state_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x →
    Rows.IsotInternal (Dof x).what₂ → GlobalTheory.EigRows.OccGood (Dof x) →
    ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ)
      (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), (∀ kk, θ kk ≠ 1) →
      LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → (∀ j Pl, hL' j 0 Pl = 1) →
      HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' →
      ∀ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig →
        SpanC (SOf x) (SbD (Dof x)) θ hL' eig := by
  intro hL
  refine (((_root_.GlobalTheory.T.mem_goodL_iff_iotaR_mem_goodW hL).and (_root_.GlobalTheory.T.iotaR_injective_at_level_a hL)).and (_root_.GlobalTheory.T.exists_hkDat_at_split_place hL)).trans (StepW.of_all fun K B f T w _ _ h => ?_)
  obtain ⟨⟨htie, hinj⟩, hhk⟩ := h
  intro P x hLA hI hG θ hL' hθ hlv _ _ hRd eig hEig
  exact spanC_core x.m.z.R x.m.z.F x.r.Y x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) θ hL' eig hI hG
    (htie P x hLA θ hθ hlv) (hinj P x hLA) (hhk P x hLA) hRd hEig
end GlobalTheory.EigSpanDesc
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_c_of_stab_c_hecke_rd_eig_ad : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → Rows.IsotInternal (Dof x).what₂ → GlobalTheory.EigRows.OccGood (Dof x) → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), (∀ kk, θ kk ≠ 1) → LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → (∀ j Pl, hL' j 0 Pl = 1) → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig → SpanC (SOf x) (SbD (Dof x)) θ hL' eig := by
  atlas_forward_decl _root_.GlobalTheory.EigSpanDesc.spanC_of_state_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.RatSide
theorem eigenspace_span_of_isotypicInternal_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), (∀ kk, θ kk ≠ 1) → LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → (∀ j Pl, hL' j 0 Pl = 1) → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∃ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig ∧ SpanC (SOf x) (SbD (Dof x)) θ hL' eig := by
  intro hN hIso hL
  refine (StepW.and (StepW.and (_root_.GlobalTheory.HeightCounting.RatSide.exists_eigAd_of_state_alt hL) (_root_.GlobalTheory.T.span_c_of_stab_c_hecke_rd_eig_ad hL)) (StepW.and (_root_.GlobalTheory.T.allSt_goodFTAll_of_levelA hN hL) hIso)).trans
    (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx θ hL' h1 h2 h3 h4 h5
  obtain ⟨eig, he⟩ := H.1.1 P x hx hL' h3 h5
  exact ⟨eig, he, H.1.2 P x hx (H.2.2 P x) (GlobalTheory.EigRows.occGood_of_all _ (H.2.1 P x hx)) θ hL' h1 h2 h3 h4 h5 eig he⟩
end GlobalTheory.HeightCounting.RatSide
end
end
end
