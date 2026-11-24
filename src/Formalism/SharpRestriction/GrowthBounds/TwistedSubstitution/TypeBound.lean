module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
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

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G

def TypeBound : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι)
    (e : (Fin n → ℤ) → Module.End K (MvPolynomial (ι × Fin n) K)),
    (∀ mu, IsIsoProj (glOps K n LL S) mu (e mu)) →
    (∀ G : MvPolynomial (ι × Fin n) K, ∃ T : Finset (Fin n → ℤ),
      G = ∑ mu ∈ T, e mu G ∧ ∀ mu, e mu G ∈ isoSub (glOps K n LL S) mu) →
    ∀ (G : MvPolynomial (ι × Fin n) K) (lam : Fin n → ℤ), e lam G ≠ 0 →
      (∀ M : ℤ, lam1S LL S G ≤ (M : WithBot ℤ) → lam 0 ≤ M) ∧
      (∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → th ≤ lam (lastIdx n))

end Formalism.MainNotions.TestSideWords
