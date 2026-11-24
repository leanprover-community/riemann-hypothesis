module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

variable {E : Type} [Field E] [NumberField E]

@[reducible] def resField (PP : Pl E) : Field (kP PP) :=
  haveI := PP.isMaximal
  Ideal.Quotient.field PP.asIdeal

attribute [local instance] resField

theorem finite_res (PP : Pl E) : Finite (kP PP) :=
  Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot

attribute [local instance] finite_res

def IsIndCuspChar (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K] (s : K →+* ℂ) (χ : G0 Pg r → K) : Prop :=
  ∃ (b : ↥Pg → Fin r → ℕ) (V : ↥Pg → Type) (_ : ∀ PP, AddCommGroup (V PP)) (_ : ∀ PP, Module ℂ (V PP))
    (_ : ∀ PP, FiniteDimensional ℂ (V PP))
    (σ : ∀ PP : ↥Pg, Representation ℂ (blockTri (κ := kP PP.1) (b PP)) (V PP)),
    (∀ PP : ↥Pg, IsCuspDatum (F := kP PP.1) (b PP) (σ PP)) ∧
    ∀ g : G0 Pg r, s (χ g) =
      ∏ PP : ↥Pg, LinearMap.trace ℂ _ (parInd (F := kP PP.1) (b PP) (σ PP) (g PP))

theorem finite_parInd {F : Type} [Field F] [Finite F] {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) :
    FiniteDimensional ℂ (Representation.coindV (blockTri (κ := F) b).subtype σ) := inferInstance

def GenericMultOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (K : Type) [Field K] [CharZero K] (s : K →+* ℂ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K), IsGenericPsi Pg ψ →
    ∀ χ : G0 Pg r → K, IsIndCuspChar Pg r s χ →
      letI : Fintype (P0 Pg r ψ).H := Fintype.ofFinite _
      ∑ h : (P0 Pg r ψ).H, χ (h : G0 Pg r) * ((((P0 Pg r ψ).chi h)⁻¹ : Kˣ) : K) = (Nat.card (P0 Pg r ψ).H : K)

end GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne
