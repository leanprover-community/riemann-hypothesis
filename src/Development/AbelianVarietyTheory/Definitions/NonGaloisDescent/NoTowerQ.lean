module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import GroundTheory.LocalFields.Ramification
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField

namespace GlobalTheory.PMon.Ram


open Classical in
def jumpSum {G : Type} [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) : ℕ :=
  ∑ᶠ t : ℕ, if A ⊓ R t ≤ B then 0 else Nat.card ↥(A ⊓ R t)

section

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def wild (t : ℕ) : Subgroup (L ≃ₐ[K] L) := lowerRamificationGroup K L ((t : ℤ) + 1)

def AxIn (p : ℕ) : Prop :=
  ∀ (J : Subgroup (L ≃ₐ[K] L)) (x : L), (∀ σ ∈ J, σ x - x ∈ 𝒪[L]) →
    ∃ y : L, (∀ σ ∈ J, σ y = y) ∧ (p : L) ^ 2 * (x - y) ∈ 𝒪[L]


variable {K L} in
def Detects (p r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)) : Prop :=
  ∀ σ₀ ∈ A, σ₀ ∉ B → ∃ (x : L) (a : (L ≃ₐ[K] L) → ℤ),
    (∀ σ ∈ A, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) ∧ ¬ (p : ℤ) ^ r ∣ a σ₀

end

def OrdIs (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] (p E : ℕ) : Prop :=
  IsDiscreteValuationRing.addVal 𝒪[L] (p : 𝒪[L]) = (E : ℕ∞)

def NoTower : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (N : ℕ → Subgroup ↥(GK K)), Antitone N →
    (∀ k, IsOpen (N k : Set ↥(GK K))) →
    (∀ k, ∀ σ ∈ N k, σ ^ l ∈ N (k + 1)) →
    (∀ j, ∀ σ ∈ N 0, σ ^ l ∈ N (j + 1) → σ ∈ N j) →
    (∀ r : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (ι : Type) (_ : Finite ι) (x : ι → ℂ_[l]) (a : ι → ↥(GK K) → ℤ_[l]),
      (∀ i, ∀ σ ∈ N k, ‖Formalism.Per.σC (σ : GQ l) (x i) - x i - algebraMap ℚ_[l] ℂ_[l] (a i σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧
      ∀ σ ∈ N k, (∀ i, (l : ℤ_[l]) ^ r ∣ a i σ) → σ ∈ N (k + r)) →
    ∃ k, ∀ j, IK K ⊓ N k ≤ N j

def NoTowerQ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N : ℕ → Subgroup (GQ l)), Antitone N →
    (∀ k, IsOpen (N k : Set (GQ l))) →
    (∀ k, ∀ σ ∈ N k, σ ^ l ∈ N (k + 1)) →
    (∀ j, ∀ σ ∈ N 0, σ ^ l ∈ N (j + 1) → σ ∈ N j) →
    (∀ r : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (ι : Type) (_ : Finite ι) (x : ι → Om l) (a : ι → GQ l → ℤ),
      (∀ i, ∀ σ ∈ N k, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧
      ∀ σ ∈ N k, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N (k + r)) →
    ∃ k, ∀ j, ∀ σ ∈ N k, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → σ ∈ N j

end GlobalTheory.PMon.Ram

end
