module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DeltaPsiH
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SingleWeightOfModelIdentification
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ShapeCovering.StatementY
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

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

theorem covY_eq (K : Type) [Field K] (m : ℕ) : ShapeCovering.covY K m = covY K m := rfl

def ExplicitMapInjective : Prop := ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → Function.Injective (PsiXY K m)

def ExplicitMapOntoTwoLetters : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → ∀ (P Q : ℕ) x,
    x ∈ twoSp K m P Q ↔ ∃ f ∈ PolAB K (m + 1) P Q, PsiXY K m f = x

def TwoLetterLatticeGaussInverse : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 1 ≤ m → ∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf), IsUnit g.det →
    ∀ g' : GL (Fin (m + 1)) R.Kf, (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) = g⁻¹ →
      ∀ (P Q : ℕ), ∀ f ∈ PolAB R.Kf (m + 1) P Q,
        PsiXY R.Kf m f ∈ twoLat R.O m P Q (colSpan R.O g) ↔ f ∈ latOf g' (GaussLat R.Ov.toSubring)

end Formalism.MainNotions.flipOneThree.Pf

end
