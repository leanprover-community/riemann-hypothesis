module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTail
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreLast
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsEvalKerKrullDim
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherAlt
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem FibreDimensionZero.proof (h₁ : ArithmeticIntersectionFibreMultiHomogeneous.Statement) (h₂ : EvalKerKrullDim.Statement)
    (h₃ : FibreTranscendenceDegreeAlt.Statement) : FibreDimensionZero.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n hv hp hW hV G'
  refine ⟨⟨RingHom.ker_isPrime _, h₁ K ι K' ι' κ v p W' hv hp hW.1.2.1 G', fun k => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hW.1.2.2 k.1
    refine ⟨i, fun h => hi ?_⟩
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at h
    have hX : (X ⟨k.1, i⟩ : MRing ι') ∈ W' := by
      rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
      exact h
    simpa using Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom (ZMod p))) hX
  · rw [fibreIdeal, h₂ (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ', h₃ K ι K' ι' κ v p W' n hv hp hW hV G']
    simp

end GroundTheory.Heights₂.Heights.Inter
