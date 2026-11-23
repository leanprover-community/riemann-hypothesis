module

public import ReciprocityTheory.DualLattices.TensorSpan
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.Integers
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

noncomputable section

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def SubgroupFreenessStatement : Prop :=
  IsAlgClosed C → CharZero C →
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
    (AA : HopfOrder (C := C) R N),
    let B := AA.carrier.comap (pullQ (R := R) K)
    let AK := AA.carrier.map (resK (R := R) K)
    let IK := (augIdeal B).map (pullQ K)
    (∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ g ∈ AA.carrier,
      ∃! b : K → N → C, (∀ j, b j ∈ B.map (pullQ K)) ∧ g = ∑ j, b j * f j) ∧
    (∀ g ∈ AA.carrier, resK (R := R) K g = 0 → g ∈ IK * AA.carrier) ∧
    (∀ c cB cK, HasColen R v AA.carrier c → HasColen R v B cB → HasColen R v AK cK →
      c = cB ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K)) ∧
    (∀ g ∈ augIdeal AA.carrier, resK (R := R) K g ∈ augIdeal AK * augIdeal AK →
      g ∈ IK ⊔ augIdeal AA.carrier * augIdeal AA.carrier)

end ReciprocityTheory.PGsh.L2
