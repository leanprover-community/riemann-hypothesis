module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ElemPairJ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open ValuativeRel Matrix GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

def BallLev : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (r : ValueGroupWithZero k),
    0 < r → r < 1 → ∀ K : Subgroup (GL (Fin n) k), (K : Set (GL (Fin n) k)) = ball n r → IwLev K ∧ ∀ t, dcos K t = elemSet r {t}

def LevOf : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (r : ValueGroupWithZero k),
    0 < r → r < 1 → ∀ D : Subgroup (Fin n → kˣ), IsCompact (D : Set (Fin n → kˣ)) → (∀ d ∈ D, ∀ i, valuation k (d i : k) = 1) →
    ∃ K : Subgroup (GL (Fin n) k), (∀ g, g ∈ K ↔ ∃ a ∈ ball n r, ∃ d ∈ D, g = a * diagT k (Fin n) d) ∧ IwLev K ∧
      ∀ t, dcos K t = elemSet r {x | ∃ d ∈ D, x = t * d}

def SmallRad : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
    (∀ U : Set (GL (Fin n) k), U ∈ nhds 1 → ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ r' ≤ r, ball n r' ⊆ U) ∧
    (∀ W : Set (Fin n → kˣ), W ∈ nhds 1 → ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ r' ≤ r, ∀ u, Near r' u → u ∈ W) ∧
    (∀ r : ValueGroupWithZero k, r < 1 → ∃ D : Subgroup (Fin n → kˣ), (∀ u, u ∈ D ↔ Near r u) ∧ IsCompact (D : Set (Fin n → kˣ))) ∧
    Continuous (diagT k (Fin n)) ∧ (∃ t : Fin n → kˣ, Strict t) ∧ ∀ t₀ t : Fin n → kˣ, Strict t₀ → Dom t → Strict (t₀ * t)

end UpperTheory.Gal.InertialTypesAlt.L
