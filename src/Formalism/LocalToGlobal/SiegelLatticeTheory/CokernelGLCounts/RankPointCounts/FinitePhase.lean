module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameNormal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealPhaseFrames
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealPointRepresentatives
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.FinitePhase

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def LiftCellC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : Formalism.L2.SG.Pf.RowForm.LiftT X Y u u' κ R ρ),
    s.1.relevant →
    ∃ L U : Formalism.L2.SG.PairVal.MatR D, IsLoUni L ∧ IsUpUni U ∧
      ZhatOM (ZhatL (lf D (X.Fu u)) s.1.frame) = L * ptMat (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * U ∧
      ∀ v, Formalism.L2.SG.RealObj.ZhatO (Formalism.L2.SG.RealObj.ZX X u u' 1 s.1.pt.1 v) =
        (L * ptMat (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * U).map (fun x => X.B.I.φ v (X.ιE.symm x))

def FinPhaseC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : Formalism.L2.SG.Pf.RowForm.LiftT X Y u u' κ R ρ),
    s.1.relevant → ∀ L U : Formalism.L2.SG.PairVal.MatR D, IsLoUni L → IsUpUni U →
      ZhatOM (ZhatL (lf D (X.Fu u)) s.1.frame) = L * ptMat (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * U →
      Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) * Formalism.L2.SG.PairVal.phasePair (gS D) L U =
        Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

theorem phaseTieC_of (hC : LiftCellC X Y u u' κ) (hF : FinPhaseC X Y u u' κ) :
    Formalism.L2.SG.Pf.RowForm.PhaseTieC X Y u u' κ := by
  intro R ρ s hrel g hg g' hg' hdec
  obtain ⟨L, U, hL, hU, hrat, hreal⟩ := hC R ρ s hrel
  have hex := Formalism.L2.SG.RealObj.RealPointRepresentatives.exists_ptRep X u u' s.1.pt.1 _ L U hL hU hreal
  have hPt : Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) := by
    unfold Formalism.L2.SG.RealObj.gamW
    rw [dite_eq_left hex]
    exact hex.choose_spec
  rw [Formalism.L2.SG.RealObj.RealPhaseFrames.realPhase X u u' hg hg' hdec _ hPt L U hL hU hreal]
  exact hF R ρ s hrel L U hL hU hrat

end Formalism.L2.SG.Pf.FinitePhase
