module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFi
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

open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.edgeClass_eq_kummerCharacter_of_chosen_root_function_field : ∀ (k K Ω F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[F] Ω, g ζ = ζ) →
  (∀ τ : K ≃ₐ[F] K, ∀ x ∈ FunctionField.ringOfIntegers k K, τ x ∈ FunctionField.ringOfIntegers k K) →
  ∀ (a b : F) (α β : Ω), a ≠ 0 → b ≠ 0 → algebraMap F K a ∈ FunctionField.ringOfIntegers k K → (algebraMap F K a)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    algebraMap F K b ∈ FunctionField.ringOfIntegers k K → (algebraMap F K b)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    α ^ N = algebraMap F Ω a → β ^ N = algebraMap F Ω b →
  ∀ (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)), (∀ g, (x g).toAdd = kum (N := N) ζ α g) → (∀ g, (y g).toAdd = kum (N := N) ζ β g) →
  ∀ η : (Ω ≃ₐ[F] Ω) → ZMod N, CobOn (geo F K Ω) x y η →
    IsLocallyConstant (fun g : geo F K Ω => η g) →
    (∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω), Over (FunctionField.ringOfIntegers k K).toSubring B →
      (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo F K Ω → η g = 0) →
  ∀ σ : Ω ≃ₐ[F] Ω, IsTopW (K := K) ζ x y η σ (topW (K := K) ζ x y η σ) := by
  first | exact @GlobalTheory.K4.isTopW_topW | exact GlobalTheory.K4.isTopW_topW | (intros; apply GlobalTheory.K4.isTopW_topW <;> assumption)
