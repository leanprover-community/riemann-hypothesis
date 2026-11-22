module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqLatFrameOfIsSDFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConstMovedVacuumAllTuplesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIntegralMulVec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPrimeMemPl
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueFamilyVacuumData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorBesselExistenceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGeometricMeasureVolumeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyGeometryColumn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentVectorRelationStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataAtTypePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLevelData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentPlacesCharacterizedStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentAtSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FixLevCompactOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoExists

section Transport

variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem shape_upd {v : VCom c} {o : GlobalTheory.SeeSaw.TDat c k ι} (h : ShapeOff v o) (b Ψ ΨT JG eG eGT dG) :
    ShapeOff { v with b := b, Ψ := Ψ, ΨT := ΨT, JG := JG, eG := eG, eGT := eGT, dG := dG } o :=
  ⟨⟨h.pre.nodup, h.pre.all, h.pre.inj, h.pre.tP, h.pre.char, h.pre.latT, h.pre.line, h.pre.tau, h.pre.lam, h.pre.normT, h.pre.topT⟩,
    fun x => ⟨(h.good x).bf, (h.good x).fb⟩, fun x hx => ⟨(h.split x hx).core, (h.split x hx).top⟩, h.glued, h.rep, h.ram⟩

theorem moves_one (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) : GlobalTheory.FinPl.Moves S 1 L L P := fun y _ => by
  have e : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [e, Matrix.one_mulVec]

theorem exists_places (D : D7) (T : ℕ) (hT : T ≠ 0) : ∃ s : Finset (GlobalTheory.FinPl.Pl D), ∀ p, p ∈ s ↔ ((T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
  have h0 : Ideal.span {((T : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hT
  refine ⟨(Ideal.finite_factors h0).toFinset, fun p => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

end Transport

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word}

end Gen

end GlobalTheory.GeoExists

end
