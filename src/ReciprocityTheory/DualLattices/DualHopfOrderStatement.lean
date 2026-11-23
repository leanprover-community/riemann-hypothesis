module

public import ReciprocityTheory.DualLattices.TensorSpan
public import Mathlib.Algebra.Group.AddChar
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

def DualHopfOrderStatement : Prop :=
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N H : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] [AddCommGroup H] [Fintype H]
    [DecidableEq H] (e : H ≃ AddChar N C), (∀ h h', e (h + h') = e h * e h') →
    Fintype.card H = Fintype.card N →
    ∀ AA : HopfOrder (C := C) R N,
      ∃ AD : HopfOrder (C := C) R H,
        AD.carrier = (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) ∧
        (dualLat AD.carrier).map (fourier (R := R) fun a h => e h a) = AA.carrier ∧
        ∀ c c', HasColen R v AA.carrier c → HasColen R v AD.carrier c' →
          (c * c') ^ 2 = v (Fintype.card N : C) ^ Fintype.card N

end ReciprocityTheory.PGsh.L2
