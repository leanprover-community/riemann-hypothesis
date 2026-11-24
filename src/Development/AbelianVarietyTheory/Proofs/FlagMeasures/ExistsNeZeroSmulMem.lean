module

import Lemmata.GeneralBFactThirdRest.Imports
public import Formalism.LocalRingCardinality.DataSpaces
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

namespace GlobalTheory.NonzeroIntegerSmulMem

theorem exists_ne_zero_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : Formalism.BasicNotions.HSpace E} (L : Submodule (RingOfIntegers E) (Formalism.BasicNotions.HSpace.V S))
    (hL : Submodule.IsFullLattice E L) (x : Formalism.BasicNotions.HSpace.V S) :
    ∃ r : RingOfIntegers E, r ≠ (0 : RingOfIntegers E) ∧ r • x ∈ L := by
  apply Bl.general_b_fact_third''''.goal1 <;> assumption

end GlobalTheory.NonzeroIntegerSmulMem
