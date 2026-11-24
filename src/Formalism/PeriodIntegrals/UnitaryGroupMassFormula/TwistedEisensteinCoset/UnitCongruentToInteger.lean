module

public import Formalism.PeriodIntegrals.TwistedEisensteinNonvanishing
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

def IntegerIntegralIffDvd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ i e : ℕ, IntAt P ((i : E) / (qOf P : E) ^ e) ↔ qOf P ^ e ∣ i

def IntegralApproximationByInteger : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (x : E) (N : ℕ), IntAt P x → ∃ i : ℕ, i < qOf P ^ N ∧ IntAt P ((x - i) / (qOf P : E) ^ N)

def ElementEqPrimePowerMulUnit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ a : E, a ≠ 0 → ∃ (e : ℤ) (w : E), a = (qOf P : E) ^ e * w ∧ w ≠ 0 ∧ IntAt P w ∧ IntAt P w⁻¹

def ValuationExponentUnique : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (e e' : ℤ) (w w' : E), w ≠ 0 → IntAt P w → IntAt P w⁻¹ → IntAt P w' → IntAt P w'⁻¹ →
      (qOf P : E) ^ e * w = (qOf P : E) ^ e' * w' → e = e'

def UnitCongruentToInteger : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (w : E) (N : ℕ), w ≠ 0 → IntAt P w → IntAt P w⁻¹ →
      ∃ w0 : ℕ, Nat.Coprime w0 (qOf P) ∧ IntAt P ((w - w0) / (qOf P : E) ^ N)

end PI.TwistedEisensteinNonvanishing.W
