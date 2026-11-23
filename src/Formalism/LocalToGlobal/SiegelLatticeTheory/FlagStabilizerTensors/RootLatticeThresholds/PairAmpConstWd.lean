module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCountEqHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PvalFormExistsRf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem ooIntAll_of (hWD : Formalism.L2.SG.WuDecay.WuDecay X) (w w' : D.what₂.Word) :
    OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w') :=
  Formalism.L2.SG.Closed.OOIntAllC_outright D X Y w w'
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y w (Formalism.L2.SG.Closed.level_subgroup_properties X) hWD)
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y w' (Formalism.L2.SG.Closed.level_subgroup_properties X) hWD)
    (Formalism.L2.SG.Pf.fundExistsC_holds D X Y w w')

variable {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

theorem pvalForm_holds (hWD : Formalism.L2.SG.WuDecay.WuDecay X) : ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists_oi W hI (ooIntAll_of hWD) (Formalism.L2.SG.Pf.FibreEq.FibreCountEq_holds hF)

end Formalism.L2.SG.Pf.KernelOfEmbedding
