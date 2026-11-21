import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarsOfGivenData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraNodesFarApartOfCubicNodeGap
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionOnAdelicFunctionsEqZeroOfNoLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointInjOfParts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointKeepsSphericalPartsOffTuple

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.ScalarsRow

theorem scalars_of_heckeFormNS : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite →
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram →
    GlobalTheory.Published.UnramifiedDoublingGL → (∀ D : D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D) →
    ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
      [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  intro hDS hHCF hHCM hCW hCusp hHowe hUD hHk D G _ _ Pl0 T A Ks _ _ _ R F hG
  obtain ⟨L, ⟨P⟩⟩ := hG.params
  exact GlobalTheory.T.thetaChain_steps_positive_multiple_of_LValue hHCF hCusp hDS hHCM hCW hHowe hUD R F hG
    (GlobalTheory.Core.Rk.GapOfNodes.harishChandraNodesFarApart_of_cubic_node_gap D (by simpa using P.nodeGap_ge_cubic_rank)) (hHk D)

theorem scalars : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  intro hDS hHCF hHCM hCW hCusp hHowe _ hHk _ hUD D G _ _ Pl0 T A Ks _ _ _ R F hG _
  exact scalars_of_heckeFormNS hDS hHCF hHCM hCW hCusp hHowe hUD hHk R F hG

end GlobalTheory.Core.Rk.ScalarsRow
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStep_positive_scalar_standingHypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  atlas_forward_decl GlobalTheory.Core.Rk.ScalarsRow.scalars
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.UpInjScal

theorem exists_lvals {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hsc : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R) (t : T) (c : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.EigSys D)
    (hne : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c ≠ ⊥) :
    ∃ z : Fin D.R.m → ℝ, (∀ i, 0 < z i) ∧ ∀ i, IsLval R i t c (z i) := by
  obtain ⟨κ, -, hs⟩ := hsc
  obtain ⟨⟨B, hB⟩, hall⟩ := hs t c hne
  obtain ⟨hstep, htop⟩ := hall B hB
  have h : ∀ i : Fin D.R.m, ∃ l, GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsLValue R t B ((i : ℕ) + 1) l := by
    intro i
    by_cases hi : (i : ℕ) + 1 < D.R.m
    · obtain ⟨l, hl, -⟩ := hstep i hi
      exact ⟨l, hl⟩
    · have e : (i : ℕ) + 1 = D.R.m := by omega
      obtain ⟨l, hl, -⟩ := htop
      exact ⟨l, by rw [e]; exact hl⟩
  choose z hz using h
  exact ⟨z, fun i => (hz i).2.1, fun i => ⟨B, hB, hz i⟩⟩

end GlobalTheory.Core.Rk.UpInjScal

open GlobalTheory.Hk3 in

theorem GlobalTheory.Core.Rk.upInj_of_bForm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → BForm R SF → UpInj R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hI hsc SF hSF hB
  obtain ⟨κ₀, hκ₀, hE⟩ := hB
  have hM := hC.models
  have hs : ∀ (t : T) (c : Eig D), ∃ s : ℝ, 0 < s ∧ ∀ x ∈ EEc R SF c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((s : ℝ) : ℂ) • x := by
    intro t c
    by_cases hne : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c = ⊥
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have h1 : R.HE.e x ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c :=
        (GlobalTheory.ChainScalar.mem_rowPart (R := R) hM.HE).1 (GlobalTheory.ChainScalar.eec_le (R := R) hSF t c hM.HE hx)
      rw [hne, Submodule.mem_bot] at h1
      have hx0 : x = 0 := hM.HE.1 (h1.trans (LinearMap.map_zero _).symm)
      subst hx0
      exact ((congrArg (R.Th t) (LinearMap.map_zero _)).trans (LinearMap.map_zero _)).trans (smul_zero _).symm
    · have hz0 : ∃ z : Fin D.R.m → ℝ, (∀ i, 0 < z i) ∧ ∀ i, IsLval R i t c (z i) :=
        GlobalTheory.Core.Rk.UpInjScal.exists_lvals (T := T) R hsc t c hne
      obtain ⟨z, hz, hl⟩ := hz0
      exact ⟨κ₀ * ∏ i, z i, mul_pos hκ₀ (Finset.prod_pos fun i _ => hz i), hE t c z hl⟩
  intro t
  choose s hs0 hsE using hs t
  refine (injective_iff_map_eq_zero _).2 fun x h0 => ?_
  obtain ⟨h, -, -, hsp, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
  refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.Th t) (fun c => EEc R SF c) (fun c => ((s c : ℝ) : ℂ))
    (fun c => Complex.ofReal_ne_zero.2 (hs0 c).ne') (fun c x hx => hsE c x hx) ?_ h0
  rw [hsp]; trivial
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.UpInjRow

theorem upInj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → R.Sb = R.Pg → (∀ t P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R t P) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → BForm R SF ∧ UpInj R := by
  intro hDS hHCF hHCM hCW hCRD hHowe hWS hHecke hSEC hUD D G _ _ Pl0 T A Ks _ _ _ R F hGiv hcc _hSb hFix SF hSF
  have hSc := GlobalTheory.T.thetaChainStep_positive_scalar_standingHypotheses hDS hHCF hHCM hCW hCRD hHowe hWS hHecke hSEC hUD R F hGiv hcc
  have hK := GlobalTheory.T.thetaLift_adjoint_keeps_spherical_parts_off_tuple hCRD hHowe R F hGiv.core hFix
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R
  have hB := GlobalTheory.ChainScalar.bForm R F hGiv.core hS hSc hK SF hSF
  exact ⟨hB, GlobalTheory.Core.Rk.upInj_of_bForm R F hGiv.core hS hGiv.irr hSc SF hSF hB⟩

end GlobalTheory.Core.Rk.UpInjRow
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_adjoint_scalarFormula_injective : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → R.Sb = R.Pg → (∀ t P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R t P) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → BForm R SF ∧ UpInj R := by
  atlas_forward_decl GlobalTheory.Core.Rk.UpInjRow.upInj
end
