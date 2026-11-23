module

public import Formalism.TameInertiaTowers.InvLength
public import Formalism.TameInertiaTowers.StatementField
public import Formalism.TameInertiaTowers.CentralOrderTwo.ConjEqInvOfPowEqOne
public import Formalism.TameInertiaTowers.CentralOrderTwo.DecompositionSubgroupIndex
public import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
public import Formalism.TameInertiaTowers.CentralOrderTwo.Groups
public import Formalism.TameInertiaTowers.CentralOrderTwo.MemDecompositionSubgroupIff
public import Formalism.TameInertiaTowers.CentralOrderTwo.NegOneNeOneUnitsZmodFour
public import Formalism.TameInertiaTowers.CentralOrderTwo.NormalOrderTwoCentral
public import Formalism.TameInertiaTowers.CentralOrderTwo.OddEqOneOfSubOneMem
public import Formalism.TameInertiaTowers.CentralOrderTwo.OrderOfThreeUnitsTwoPow
import Formalism.TameInertiaTowers.CentralOrderTwo.TwoAdic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

namespace Formalism.TwoAdicCyclotomicDecomposition

theorem layerConj : LayerConj := layerConj_of layerGalois
theorem layerReal : LayerReal := layerReal_of layerGalois layerConj
theorem layerDecompTwo : LayerDecompTwo := layerDecompTwo_of layerGalois
theorem layerInertiaTwo : LayerInertiaTwo := layerInertiaTwo_of layerGalois
theorem layerEFGTwo : LayerEFGTwo := layerEFGTwo_of layerGalois layerReal
theorem layerInertiaTame : LayerInertiaTame := layerInertiaTame_of layerGalois
theorem layerFrob : LayerFrob := layerFrob_of layerGalois

theorem tower_field_foundations :
    LayerExists ∧ LayerGalois ∧ LayerConj ∧ LayerReal ∧ LayerDecompTwo ∧ LayerInertiaTwo ∧
    LayerEFGTwo ∧ LayerInertiaTame ∧ LayerFrob :=
  ⟨layerExists, layerGalois, layerConj, layerReal, layerDecompTwo, layerInertiaTwo, layerEFGTwo,
    layerInertiaTame, layerFrob⟩

theorem towerProperties :
    (UnitsTwoPow ∧ QuotCyclic ∧ TwoAdicOrder ∧ TwoAdicVal ∧ DecompModel ∧ GmRank ∧ GensModel ∧
      GamEModel ∧ GGModel ∧ CentralExtAbelian ∧ CommGen ∧ RankBound ∧
      NormalOrderTwoCentral ∧ TwistVal ∧ CoinvLength ∧ PGroupGen ∧ GenusModel ∧ GenusAbelian) ∧
    InvLength ∧
    (LayerExists ∧ LayerGalois ∧ LayerConj ∧ LayerReal ∧ LayerDecompTwo ∧ LayerInertiaTwo ∧
      LayerEFGTwo ∧ LayerInertiaTame ∧ LayerFrob) :=
  ⟨⟨unitsTwoPow, quotCyclic, twoAdicOrder, twoAdicVal, decompModel, gmRank, gensModel, gamEModel,
      ggModel, centralExtAbelian, commGen, rankBound,
      normalOrderTwoCentral, twistVal, coinvLength, pGroupGen, genusModel, genusAbelian⟩,
    invLength, tower_field_foundations⟩

end Formalism.TwoAdicCyclotomicDecomposition
