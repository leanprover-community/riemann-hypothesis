module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

variable {F : Type} [Field F] [NumberField F]

def LocMem (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (z : F) : Prop :=
  ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ y ∈ I, (s : F) * z = (y : F)

def cosetOff {ι : Type} (S : Finset (HeightOneSpectrum (𝓞 F))) (I : Ideal (𝓞 F)) (x0 : ι → F) : Set (ι → F) :=
  {x | ∀ v, v ∉ S → ∀ i, LocMem I v (x i - x0 i)}

def latCoset {ι : Type} (I : Ideal (𝓞 F)) (x0 : ι → F) : Set (ι → F) :=
  {x | ∀ i, ∃ y ∈ I, (y : F) = x i - x0 i}

def ballV (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : Set (Fv F v) :=
  {z | Valued.v z ≤ WithZero.exp (-(k : ℤ))}

def boxInd {ι : Type} (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (c y : ι → Fv F v) : ℝ :=
  if ∀ i, y i - c i ∈ ballV v k then 1 else 0

def term {ι : Type} (θ : ℝ →+* Ainf F) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (ι → Ainf F) → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ) (ε : ℝ) (x : ι → F) : ℝ :=
  φ (fun i => θ ε * algebraMap F (Ainf F) (x i)) * ∏ v ∈ S, ψ v fun i => algebraMap F (Fv F v) (x i)

end GlobalTheory.CompanionTheory.Equi

end
