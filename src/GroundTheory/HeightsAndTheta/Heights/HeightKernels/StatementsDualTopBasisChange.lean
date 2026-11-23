module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
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

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def DualTopBasisChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T₂ : Type) [Fintype T]
    [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b₂ : Module.Basis T₂ ℤ (dualLattice F))
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T₂) (dualIdeal b₂) i (fun _ => dualLine F b₂ hb₂) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb)

def dualBasisStandardNeg : Module.Basis (Fin 1) ℤ (dualLattice (HermLattice.standard ℚ 1)) :=
  (dualBasisStandard.map (LinearEquiv.neg ℤ)).reindex (Equiv.ofUnique Unit (Fin 1))

end

end GroundTheory.Heights₂.Heights
