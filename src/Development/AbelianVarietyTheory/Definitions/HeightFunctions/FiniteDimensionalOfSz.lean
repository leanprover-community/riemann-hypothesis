module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain

def Sz (F : IntermediateField ℚ ℂ) (a b : ℝ) : Prop :=
  ∃ _ : FiniteDimensional ℚ F, letI : NumberField F := NumberField.mk
    Real.log (Module.finrank ℚ F) ≤ a ∧ Real.log |((NumberField.discr F : ℤ) : ℝ)| / Module.finrank ℚ F ≤ b

def IsRay {K : Type} [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)) : Prop :=
  (∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → GlobalTheory.NT.UnramIn L 𝔭) ∧
  Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ GlobalTheory.NT.IsFrob L 𝔭 σ} = ⊤ ∧
  ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
    ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, GlobalTheory.NT.heckeIdeal L χ I = 1) ↔
      ∃ α β : 𝓞 K, GlobalTheory.NT.RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α})

def weberSet (L : PeriodPair) (n : ℕ) : Set ℂ :=
  insert (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2))
    {w | ∃ z ∈ L.lattice, z / n ∉ L.lattice ∧ w = L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (z / n)}

theorem finiteDimensional_of_sz {F : IntermediateField ℚ ℂ} {a b : ℝ} (h : Sz F a b) : FiniteDimensional ℚ F := h.1

end GlobalTheory.FieldSize
