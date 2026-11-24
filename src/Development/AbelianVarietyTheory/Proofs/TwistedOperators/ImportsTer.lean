module

import Formalism.LocalToGlobal.IndefiniteReal.MemSpanOfSmulMem
public import Mathlib.NumberTheory.NumberField.Basic
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

namespace GlobalTheory.TargetStatementSixOneSixtyEight

open NumberField

theorem main {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) {y : V} (hy : y ∈ Submodule.span E (L : Set V)) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ c • y ∈ L := by
  apply Formalism.IndefR.LatticeTransfer.Lat.exists_smul_mem <;> assumption

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module E V] [inst_4 : Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    (L : Submodule (NumberField.RingOfIntegers E) V) {y : V},
    y ∈ Submodule.span E (↑L : Set V) →
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ L :=
  fun L _ hy => main L hy

end GlobalTheory.TargetStatementSixOneSixtyEight
