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
import Mathlib.Tactic.Linter.HaveILetI
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

def IsCuspIndChar {F : Type} [Field F] {r : ℕ} (θ : GL (Fin r) F → ℂ) : Prop :=
  ∃ (b : Fin r → ℕ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (σ : Representation ℂ (blockTri (κ := F) b) V),
    IsCuspDatum b σ ∧ ∀ g : GL (Fin r) F, θ g = LinearMap.trace ℂ _ (parInd b σ g)

abbrev kField {E : Type} [Field E] [NumberField E] (PP : Pl E) : Field (kP PP) :=
  Ideal.Quotient.field PP.asIdeal

def IsCuspIndProdChar {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K]
    (s : K →+* ℂ) (χ : G0 Pg r → K) : Prop :=
  ∃ θ : ∀ PP : ↥Pg, GL (Fin r) (kP PP.1) → ℂ,
    (∀ PP : ↥Pg, @IsCuspIndChar (kP PP.1) (kField PP.1) r (θ PP)) ∧
    ∀ g : G0 Pg r, s (χ g) = ∏ PP : ↥Pg, θ PP (g PP)

theorem finite_boundedLevelClassGroupFamily {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) : Finite (G0 Pg r) := by
  haveI : ∀ PP : ↥Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : ∀ PP : ↥Pg, Finite (GL (Fin r) (kP PP.1)) := fun PP => inferInstance
  exact Pi.finite

abbrev fintypeH {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [CommRing K]
    (P : LevelP Pg r K) : Fintype P.H :=
  haveI := finite_boundedLevelClassGroupFamily Pg r
  Fintype.ofFinite _

def lvlSum {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K]
    (P : LevelP Pg r K) (χ : G0 Pg r → K) : K :=
  letI := fintypeH P
  ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K)

def OneWhittakerVector : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (K : Type) [Field K] [CharZero K] (s : K →+* ℂ) (ψ : ∀ PP : Pl E, AddChar (kP PP) K),
    IsGenericPsi Pg ψ →
    ∀ χ : G0 Pg r → K, IsCuspIndProdChar Pg r s χ →
      lvlSum (P0 Pg r ψ) χ = (Nat.card (P0 Pg r ψ).H : K)

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter
