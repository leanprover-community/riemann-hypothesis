module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.DatumToG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CongL
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G1

def AuxiliaryInertOddPrime : Prop := ∀ d : ℕ, 0 < d → ∀ b : ℕ, ∃ (p : ℕ) (_ : Fact p.Prime), b < p ∧ IsSquare (-(d : ℚ_[p]))

def ArithK : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ), 0 < d → ∀ x : E, x ^ 2 = -(d : E) →
  ∀ (τ₀ : E →+* ℂ) (Q : Finset ℕ), (∀ q ∈ Q, ∃ _ : Fact q.Prime, IsSquare (-(d : ℚ_[q]))) →
  ∃ A : Arith E, A.τ₀ = τ₀ ∧ (∃ f : ℚ, f ≠ 0 ∧ 2 * (A.ω : E) - (A.tr : E) = (f : E) * x) ∧
    (∀ (q : ℕ) [Fact q.Prime], IsSquare (-(d : ℚ_[q])) → A.SplitK q) ∧ ∀ q ∈ Q, A.Good q

def ScOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Even (Module.finrank ℚ (maximalRealSubfield E)) →
  ∀ (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p), Odd n → Sc S.D S.G

def RootAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (q : ℕ), q.Prime → A.SplitK q →
  ∀ w : HeightOneSpectrum (𝓞 E), (q : 𝓞 E) ∈ w.asIdeal →
  ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - A.tr * r + A.nm ∧ A.ω - (r : 𝓞 E) ∈ w.asIdeal

end UpperTheory.Gal.G1
