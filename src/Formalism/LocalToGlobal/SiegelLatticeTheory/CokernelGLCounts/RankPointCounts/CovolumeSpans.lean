module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vector_eq_zero_of_orbital_zero {D : D7} {X : HidaSetting D} (Y : Full X) {u : D.what₂.Word} (t : GTu Y u)
    (h : OOt t = 0) : (Y.tO u u).vec t = 0 := by
  unfold Full.tO tOf
  dsimp only
  unfold vec ampN
  rw [h]
  simp only [map_zero, smul_zero, ite_self]
  first
    | rfl

theorem irrVec_nohyp {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (t : GTu Y u) (ht : ¬ t.relevant) :
    (Y.tO u u).vec t = 0 :=
  vector_eq_zero_of_orbital_zero Y t
    (Vanish.ooVanish_of _root_.Formalism.L2.SG.TermOp.Vanish.avgCore Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
      _root_.Formalism.L2.SG.Pf.chiTrivialC_outright Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds
      Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t ht)

theorem IrrVecC_holds : IrrVecC := by
  intro D X Y u _ _ t _ ht
  exact irrVec_nohyp Y u t ht

end Formalism.L2.SG.KappaOffDiagonal
