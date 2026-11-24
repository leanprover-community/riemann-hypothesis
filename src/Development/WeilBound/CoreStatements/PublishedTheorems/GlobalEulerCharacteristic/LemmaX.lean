module

public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN

def GlobalEulerCharCoprime : Prop :=
  ∀ (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))), S.Finite → ∀ (ℓ : ℕ) [Fact ℓ.Prime],
    (∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) → ∀ (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 (AlgebraicClosure ℚ) x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S),
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)).Normal →
    Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)).index ℓ →
    (∃ ζ : L.1, IsPrimitiveRoot ζ ℓ) → (ℓ ≠ 2 ∨ IsTotallyComplex L.1) →
    ∀ (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
      (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)) [IsDiscreteRep M] [Finite M],
      (∀ m : M, ℓ • m = 0) →
      (∀ g ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)), M.ρ g = 1) →
      gsEulerRatio S M ιr = 1

end PositivityTheory.Lit1.GEN
