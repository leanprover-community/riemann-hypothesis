module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.TypedNeOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelSOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLeMaximalCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.InLevelSAtOf
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

namespace MassDataLevelSSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

theorem inLevelSAt_of_parts (hLS : LevelSAll) (a1 : KSpCompact) (a2 : KSpOpen) (b1 : CMInst) (b2 : FrameStd)
    (b3 : LatAdapted) (b4 : ProdNH) (b5 : GlobFromParts) (c1 : HaarIdxLoc) (c2 : HaarIdxGlob) (c3 : LocLevi)
    (c4 : GlobProd) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  inLevelSAt_of (typedNe_of a1 a2) (b5 hLS b1 b2 b3 b4) (ratioH_of c1 c2 c3 c4)

end MassDataLevelSSteps
