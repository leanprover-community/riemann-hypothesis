module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeShapeExistsProofStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMoveSelfDualLatticeSplitFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEqStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChainStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelationStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValueStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalarStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquationStatement

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LatShape

theorem coreFrame_beta_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n)
    {F F' : Frame k B.V₀.rank (n ⊕ Unit)} (h : p.IsCoreFrame B s FA F) (h' : p.IsCoreFrame B s FA F') : F.β = F'.β := by
  ext r (a | u)
  · rw [h.1, h'.1]
  · cases u
    rw [h.2, h'.2]

end GlobalTheory.Fam.LatShape

end
