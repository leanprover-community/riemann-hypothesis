module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Mathlib.RingTheory.DedekindDomain.Different
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

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal

variable {E : Type} [Field E] [NumberField E]

def IsCMType {I : Type} (φ : I → E →+* ℂ) : Prop :=
  ∀ σ : E →+* ℂ, ∃! i, σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)

def UnramFin (E : Type) [Field E] [NumberField E] : Prop := differentIdeal (OF E) (𝓞 E) = ⊤

def Over (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E)) : Prop :=
  P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) = v.asIdeal

def Splits (v : HeightOneSpectrum (OF E)) : Prop := ∃ P P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧ Over P v ∧ Over P' v

def expIn (𝔣 : Ideal (OF E)) (v : HeightOneSpectrum (OF E)) : ℕ := multiplicity v.asIdeal 𝔣

def IsBaseCond (𝔣 : Ideal (OF E)) : Prop :=
  𝔣 ≠ ⊥ ∧ 𝔣 ≠ ⊤ ∧ ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 → Splits v ∧ expIn 𝔣 v ≤ 2 ∧
    ∃ l : ℕ, l.Prime ∧ l ≠ 2 ∧ (l : OF E) ∈ v.asIdeal ∧ ¬ (l : ℤ) ∣ discr E ∧
      ∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = l

def IsFinSetSplitPlacesCoprimeConductor (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Prop :=
  ∀ q ∈ Q, Splits q ∧ ¬ q.asIdeal ∣ 𝔣

def condQ (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Ideal (OF E) := 𝔣 * ∏ q ∈ Q, q.asIdeal

def IsValChar {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E))
    (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) : Prop :=
  IsUnitary χ ∧ TrivOnF χ ∧ HasInf χ φ (fun i => (κ i : ℤ) + s) ∧
    ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)), Over P v →
      (v ∈ Q → LevelLe χ P 1) ∧ (v ∉ Q → ExpAt χ P (expIn 𝔣 v))

def IntAt (l : ℕ) (a : ℂ) : Prop := ∃ n : ℕ, n.Coprime l ∧ IsIntegral ℤ ((n : ℂ) * a)

def UnitAt (l : ℕ) (a : ℂ) : Prop := a ≠ 0 ∧ IntAt l a ∧ IntAt l a⁻¹

def LInf {I : Type} [Fintype I] (m : I → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (2 * (2 * (Real.pi : ℂ)) ^ (-(s + (|m i| : ℤ))) * Complex.Gamma (s + (|m i| : ℤ)))

end GlobalTheory.CMVal
