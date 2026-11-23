module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleEmbedNumbersSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleHilbertSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleSecsSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleDegree
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleDim
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem VeryAmpleEmbed.Numbers.proof (hSecs : VeryAmpleSecs.Statement.{u, w})
    (hHilb : VeryAmpleHilbert.Statement.{u, w}) : VeryAmpleEmbed.Numbers.Statement.{u, w} := by
  intro k _ Ω _ _ N y Q r h hV n hZ
  exact ⟨VeryAmpleDim.proof k Ω N y n Q r h hZ hV,
    VeryAmpleDegree.proof VeryAmpleDim.proof hSecs hHilb k Ω N y n Q r h hZ hV⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
