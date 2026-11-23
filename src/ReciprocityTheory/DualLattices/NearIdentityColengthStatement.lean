module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.Trace.Defs
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

namespace ReciprocityTheory.PGsh

open Matrix

def CharTableStatement : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (e : G ≃ AddChar G K),
    (Matrix.of fun g h : G => e h g).det ^ 2 = (Fintype.card G : K) ^ Fintype.card G ∨
    (Matrix.of fun g h : G => e h g).det ^ 2 = -(Fintype.card G : K) ^ Fintype.card G

def GaussCongruenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (O : Type) [CommRing O] [IsDomain O] (m : Ideal O) [m.IsPrime]
    (ι : F →+* O ⧸ m) (ω : MulChar F O) (ζ : O),
    Fintype.card F ≠ 2 → ζ ^ p = 1 → (∀ a, Ideal.Quotient.mk m (ω a) = ι a) →
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    ∃ y ∈ m, (∑ a : F, ω⁻¹ a * ζ ^ (Algebra.trace (ZMod p) F a).val) = (ζ - 1) * (y - 1)

end ReciprocityTheory.PGsh
