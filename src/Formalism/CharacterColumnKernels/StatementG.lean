module

public import Formalism.CharacterColumnKernels.Statement
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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

open Finset

noncomputable section

namespace Formalism.NG

def bigRect {R O : Type*} [CommRing O] {m g d : Type*} (ρ : R → Matrix d d O) (P : Matrix m g R) :
    Matrix (m × d) (g × d) O :=
  fun p q => ρ (P p.1 q.1) p.2 q.2

def StatGeneric : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O R]
    [Infinite (IsLocalRing.ResidueField O)]
    (m g s : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype s]
    (d : s → Type) [∀ w, Fintype (d w)] [∀ w, DecidableEq (d w)]
    (ρ : ∀ w, R →ₐ[O] Matrix (d w) (d w) O), (∀ w, Function.Surjective (ρ w)) →
    ∀ P : Matrix m g R, ∃ C : Matrix g m R, ∀ w,
      Module.length O (LinearMap.ker (matQ O (bigMat (ρ w) (C * P)))) =
        Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρ w) P)))

def StatGenericFin : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O R]
    (m g s : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype s]
    (d : s → Type) [∀ w, Fintype (d w)] [∀ w, DecidableEq (d w)],
    ((Fintype.card g * ∑ w, Fintype.card (d w) : ℕ) : Cardinal) <
      Cardinal.mk (IsLocalRing.ResidueField O) →
    ∀ (ρ : ∀ w, R →ₐ[O] Matrix (d w) (d w) O), (∀ w, Function.Surjective (ρ w)) →
    ∀ P : Matrix m g R, ∃ C : Matrix g m R, ∀ w,
      Module.length O (LinearMap.ker (matQ O (bigMat (ρ w) (C * P)))) =
        Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρ w) P)))

end Formalism.NG
