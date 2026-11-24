module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.IsCondAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Published

open UpperTheory.V.Sd

def HilbertEisOne : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
    IsOfFinOrder ω → (∀ v, ω.locInf v (-1) = -1) → (∀ w, IsCondAt w ω (c w)) → (∃ w, c w ≠ 0) →
    ∃ (φ : TR.Sm F 2) (L : ℂ), IsHol 1 c ω φ ∧ HasExp φ.1 1 (fun _ => L) fun 𝔪 => ∑ᶠ 𝔯 ∈ {𝔯 | 𝔯 ∣ 𝔪}, chiI ω c 𝔯

def HilbertOne : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ ι : Qbar p ≃+* ℂ, ∃ N : ℕ,
    ∀ k : ℕ, 0 < k → (p - 1) * p ^ N ∣ k → ∃ (φ : TR.Sm F 2) (c₀ : (Af F)ˣ → ℂ) (c : Ideal (𝓞 F) → ℂ),
      IsHol k (fun _ => 0) 1 φ ∧ HasExp φ.1 k c₀ c ∧ (∀ y, ‖ι.symm (c₀ y) - 1‖ < 1) ∧ ∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (c 𝔪)‖ < 1

end UpperTheory.V.Published
