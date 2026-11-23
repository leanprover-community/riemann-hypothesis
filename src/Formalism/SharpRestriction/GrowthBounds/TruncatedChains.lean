module

public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RaisingKillOfInterface
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPairOf
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.ProjectorFactorMemWeightSpace
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.YbatBase
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.YbatStep
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CnNODrop
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

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem restYB (D : Formalism.BasicNotions.D7) : RestYB :=
  restYB_of (ybat_base D restKill restPair (restPair'_of restPair)) ybat_symm

theorem raising_operators_kill_image (D : Formalism.BasicNotions.D7) : SimpleRaisingKillsExtremalProjector :=
  raising_kill_of_interface restConn restComm (restYB D) restKill

theorem extremal_projector_statement (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.adm5 D := sizes_bound_of_log_estimates D (raising_operators_kill_image D)

end Formalism.MainNotions.G.ExtremalProjector
