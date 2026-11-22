module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeMovesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStepStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesTopStepStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCombinationRebaseVacuumLatticesInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePlacesSplitIdempotentsStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CommonVac

theorem latV_eq_of_moves {D : D7} {S : HSp D} {g : GA D S} {Λ M N : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hM : GlobalTheory.FinPl.Moves S g Λ M P) (hN : GlobalTheory.FinPl.Moves S g Λ N P) :
    GlobalTheory.FinPl.latV S M P = GlobalTheory.FinPl.latV S N P := by
  have h1 : GlobalTheory.FinPl.Moves S (g * g⁻¹) M N P := GlobalTheory.StMoves.moves_mul (GlobalTheory.StMoves.moves_inv hM) hN
  rw [mul_inv_cancel] at h1
  have e1 : ∀ y : Fin S.rank → AE D, mt S (1 : GA D S) *ᵥ y = y := fun y => by
    rw [show mt S (1 : GA D S) = 1 from rfl, Matrix.one_mulVec]
  ext y
  constructor
  · intro hy
    have := (h1 y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    rwa [e1] at this
  · intro hy
    have h2 := h1 y (fun i => by
      have := GlobalTheory.FinPl.FrameLat.latV_supp hy i
      exact this)
    rw [e1] at h2
    exact h2.2 hy

end GlobalTheory.CommonVac

namespace GlobalTheory.CommonVac

end GlobalTheory.CommonVac
