module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacter
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → θ ≠ 0 → θ ^ N ∈ Set.range (algebraMap K Ω) →
  IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
  (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧ (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) := by
  first | exact @GlobalTheory.NeedB.KumLemma.kummer_character_main | exact GlobalTheory.NeedB.KumLemma.kummer_character_main | (intros; apply GlobalTheory.NeedB.KumLemma.kummer_character_main <;> assumption)
