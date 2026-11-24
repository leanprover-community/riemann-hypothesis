module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial

noncomputable section

namespace Formalism.NG

universe u

def StatBurnside : Prop :=
  ∀ (k A V : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [FiniteDimensional k V], IsSimpleModule A V →
    (∀ φ : V →ₗ[A] V, ∃ c : k, ∀ v, φ v = c • v) →
    Function.Surjective (fun a : A => DistribSMul.toLinearMap k V a)

def StatSplitAlg : Prop :=
  ∀ (T : Type u) [CommRing T] (P : T[X]), P.Monic →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (rr : Fin P.natDegree → T'),
      Module.Free T T' ∧ Module.Finite T T' ∧ Module.finrank T T' = P.natDegree.factorial ∧
      P.map (algebraMap T T') = ∏ i, (X - C (rr i)) ∧
      Algebra.adjoin T (Set.range rr) = ⊤ ∧
      ∀ (B : Type u) [CommRing B] [Algebra T B] (a : Fin P.natDegree → B),
        P.map (algebraMap T B) = ∏ i, (X - C (a i)) →
        ∃! φ : T' →ₐ[T] B, ∀ i, φ (rr i) = a i

def StatSplitFibre : Prop :=
  ∀ (T T' K : Type*) [CommRing T] [CommRing T'] [Algebra T T'] [Field K] (P : T[X]), P.Monic →
    ∀ (rr : Fin P.natDegree → T'), P.map (algebraMap T T') = ∏ i, (X - C (rr i)) →
      Algebra.adjoin T (Set.range rr) = ⊤ →
    ∀ (b : Module.Basis (Fin P.natDegree.factorial) T T') (x : T →+* K) (a : Fin P.natDegree → K),
      Function.Injective a → P.map x = ∏ i, (X - C (a i)) →
      ∀ c : Fin P.natDegree.factorial → K,
        (∀ φ : T' →+* K, φ.comp (algebraMap T T') = x → ∑ k, c k * φ (b k) = 0) → c = 0

end Formalism.NG
