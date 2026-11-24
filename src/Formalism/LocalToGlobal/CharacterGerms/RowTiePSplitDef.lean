module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Matrix.Basic
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

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePSplit

open Polynomial

def SplitSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (O : Type) [CommRing O] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : O →+* Matrix (Fin n) (Fin n) C) (P : Matrix (Fin n) (Fin n) C) (em : ι → (O →+* C)),
    P * P = P → (∀ x, P * M x = M x * P) → Function.Injective em →
    (∀ x, Polynomial.aeval (M x) (∏ c, (X - Polynomial.C (em c x))) * P = 0) →
    ∀ v : Fin n → C, ∃ w : ι → (Fin n → C), Matrix.mulVec P v = ∑ c, w c ∧ ∀ c x, Matrix.mulVec (M x) (w c) = em c x • w c

end RowTiePSplit

end Formalism.L2.FormalSeriesBounds
