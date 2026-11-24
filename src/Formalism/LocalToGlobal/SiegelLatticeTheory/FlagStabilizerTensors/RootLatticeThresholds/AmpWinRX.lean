module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.AmpWinRX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (u u' : D.what₂.Word)

theorem goodW_all (τ : D.what₂.Tau) : GoodW D τ u u' θ (locW C u u' τ) :=
  goodW_of C u u' τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u' τ) (Formalism.L2.SG.Pf.zTr C u τ)
    (Formalism.L2.SG.Pf.zTr C u' τ) (Formalism.L2.SG.Pf.haarTr C τ)

end Formalism.L2.SG.Pf.AmpWinRX
