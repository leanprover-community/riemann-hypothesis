module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
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

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace Formalism.MainNotions.NAdm

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}

def TWSet (tw : NTw R H what₂ LL0 N) (i : tw.Tw) (Q : Finset (PlE H)) : Prop :=
  ∀ v ∈ Q, IsSplitPl H v ∧ v ∉ placesOver H.E (tw.l i)

def AdmQ (tw : NTw R H what₂ LL0 N) (i : tw.Tw) (Q : Finset (PlE H)) (M : ℕ) : Prop :=
  TWSet tw i Q ∧ ∀ P ∈ Q, (∃ P' ∈ Q, IsConjPl H P P') ∧
    ∃ χ : G H.E N.Om →* Multiplicative (ZMod (tw.l i ^ M)),
      IsOpen (χ.ker : Set (G H.E N.Om)) ∧ AntiHom tw.cc χ ∧
      (∀ v ∈ placesOver H.E (tw.l i), ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
        ∀ σ ∈ Dec (F := H.E) A, χ σ = 1) ∧
      (∀ v : PlE H, v ≠ P → ¬ IsConjPl H P v → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
        ∀ σ ∈ Ine (F := H.E) A, χ σ = 1) ∧
      ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := H.E) A => Multiplicative.toAdd (χ σ)

end Formalism.MainNotions.NAdm
