module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PSelfDual
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.ModelXiOfParts
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.MovesComposeOfParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.PairingIndexBounds.Rec

theorem model_at_split_places_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.modelXi D :=
  modelXi_of_parts Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.self_dual_lattice D

theorem split_place_moves_compose (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.movesCompose D :=
  movesCompose_of_parts Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.self_dual_lattice D

end Formalism.L2.PairingIndexBounds.Rec
