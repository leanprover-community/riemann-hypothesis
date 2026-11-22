module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Formalism.LocalRingCardinality.PosOfIsomEmb

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.CommIs

open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt GlobalTheory.Core.Mi

theorem isKFin_of_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {x : M.H τ}
    (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) : Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) x := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ v hv => by
      rw [(Submodule.mem_bot _).1 hv, map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    obtain ⟨S₂, k1, k2, k3⟩ := hy
    refine ⟨S₁ ⊔ S₂, inferInstance, Submodule.add_mem_sup h2 k2, fun g hg v hv => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h3 g hg a ha) (k3 g hg b hb)
  | smul c x _ hx =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    exact ⟨S₁, h1, S₁.smul_mem c h2, h3⟩

theorem itSpans_of (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
    (aS aT : D.what₂.Tau → ℚ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hθ : IsInfFam θ) (hw : IsWeilExp ψ V W aS aT ω)
    (hv : IsVacVec ψ θ M M' f) (hi : IsItW θ M M' ω (ptOf ψ θ M M' f) It) : GlobalTheory.Core.Mi.ItSpans M M' It := by
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D V W S S' M M' θ ψ aS aT ω f It hθ hw hv hi
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap (It P) (Submodule.span ℂ
      {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y ∧ x = It P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => isKFin_of_mem _ _ (hy τ), rfl⟩
  exact hu'

end GlobalTheory.Fam.CommIs

