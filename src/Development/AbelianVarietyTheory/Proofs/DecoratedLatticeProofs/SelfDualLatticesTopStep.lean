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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopMove

section Package

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem weil_rec {n k : ℕ} (e : n = k) {χS χT : (AE D)ˣ →* Circle} {o : Om (Yc D n) D.sp.X'}
    (h : IsWeilDatumO R.ψ (Yc D n) D.sp.X' χS χT o) :
    IsWeilDatumO R.ψ (Yc D k) D.sp.X' χS χT (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') o e) := by
  subst e
  exact h

theorem vac_rec {n k : ℕ} (e : n = k) {f : WO (Yc D n) D.sp.X' → ℂ}
    (h : IsVacO R.ψ R.θ (Yc D n) D.sp.X' (cart (R.MY n)) (cart R.MX) (R.ΛY n) R.ΛX f) :
    IsVacO R.ψ R.θ (Yc D k) D.sp.X' (cart (R.MY k)) (cart R.MX) (R.ΛY k) R.ΛX
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) f e) := by
  subst e
  exact h

theorem weil_omT (hω : R.chain_ωX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO R.ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (omT R t j h) :=
  weil_rec R (idx_top h) (hω t)

theorem isVacO_vacT (hv : R.chain_vX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsVacO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (vacT R j h) :=
  vac_rec R (idx_top h) (hv t).1

end Package

end GlobalTheory.TopMove

end
