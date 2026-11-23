module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EHHre
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)


set_option smartUnfolding false in

def reY {X : HidaSetting D} (Y : Full X) : Full (reX Z X) where
  hK := (Y.hK)
  TR := (reTR Z Y.TR)
  psi_ne := (Y.psi_ne)
  what₂ := (Y.what₂)
  rowsOK := (Y.rowsOK)
  split := (Y.split)
  cs := (fun (u : @Formalism.BasicNotions.Rows.Data.Word (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.what₂ D)) ↦ @GlobalTheory.Mem.SRe.reCS D Z X u (@Formalism.L2.SG.Full.Full.what₂ D X Y u) (@Formalism.L2.SG.Full.Full.cs D X Y u))
  colReps := (Y.colReps)
  Dt := (Y.Dt)
  reps := (Y.reps)
  FN := (Y.FN)
  FN_fund := (Y.FN_fund)
  δ := (Y.δ)
  M := (Y.M)
  agree := (Y.agree)
  δ_pin := (Y.δ_pin)



def eRT {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) : RT Y u u' ≃ RT (reY Z Y) (wd Z u) (wd Z u') where
  toFun t := ⟨(t.lam), (t.mem), (t.cls)⟩
  invFun t := ⟨(t.lam), (t.mem), (t.cls)⟩
  left_inv t := (Eq.refl t)
  right_inv t := (Eq.refl t)



def eTT {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) : TT Y u u' ≃ TT (reY Z Y) (wd Z u) (wd Z u') where
  toFun t := ⟨(t.lam), (t.mem), (t.lam'), (t.mem'), (t.cls)⟩
  invFun t := ⟨(t.lam), (t.mem), (t.lam'), (t.mem'), (t.cls)⟩
  left_inv t := (Eq.refl t)
  right_inv t := (Eq.refl t)



def eCure {X : HidaSetting D} {Y : Full X} (h : FinX Y) (h' : FinX (reY Z Y)) (u : D.what₂.Word) :
    ColT (h.shInj u) ≃ₗᵢ[ℂ] ColT (h'.shInj (wd Z u)) := by
  run_tac
    let h := Lean.mkIdent `h
    let u := Lean.mkIdent `u
    let e ← Lean.Elab.Term.elabTerm (← `(LinearIsometryEquiv.refl ℂ (ColT (($h).shInj $u)))) none
    (← Lean.Elab.Tactic.getMainGoal).assign e
    Lean.Elab.Tactic.replaceMainGoal []

end GlobalTheory.Mem.SRe

end
