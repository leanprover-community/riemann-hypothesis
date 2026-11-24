module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar
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

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

def SpComp : Prop :=
  ∀ (E : Type) [Field E] (k m : ℕ) (P : Matrix (Fin k) (Fin m) E) (R : Matrix (Fin m) (Fin k) E), P * R = 1 →
    k ≤ m ∧ ∃ U : Matrix (Fin m) (Fin (m - k)) E, P * U = 0 ∧ Function.Injective U.mulVec ∧
      ∀ w : Fin m → E, P *ᵥ w = 0 → ∃ y, U *ᵥ y = w

def SpDen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (X : Matrix (Fin k) (Fin k) E), ∃ D : ℕ, 1 ≤ D ∧
    ∀ i j, (D : E) * X i j ∈ (algebraMap (𝓞 E) E).range

def SpLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (m k n d D : ℕ) (J : Matrix (Fin m) (Fin m) E)
    (M : Submodule (𝓞 E) (Fin m → E)) (V : Matrix (Fin m) (Fin k) E) (U : Matrix (Fin m) (Fin n) E),
    (J, M) ∈ Lat E m d → (∀ i, (fun r => V r i) ∈ M) → 1 ≤ D →
    (cT (starRingEnd E) V * J * V).det ≠ 0 →
    (∀ i j, (D : E) * (cT (starRingEnd E) V * J * V)⁻¹ i j ∈ (algebraMap (𝓞 E) E).range) →
    cT (starRingEnd E) V * J * U = 0 → Function.Injective U.mulVec →
    (∀ w : Fin m → E, (cT (starRingEnd E) V * J) *ᵥ w = 0 → ∃ y, U *ᵥ y = w) →
    (cT (starRingEnd E) U * J * U, M.comap ((Matrix.mulVecLin U).restrictScalars (𝓞 E))) ∈ Lat E n (d * D) ∧
    ∀ z ∈ M, ∃ c : Fin k → E, (∀ i, c i ∈ (algebraMap (𝓞 E) E).range) ∧ ∃ y : Fin n → E, U *ᵥ y ∈ M ∧
      (D : E) • z = V *ᵥ c + U *ᵥ y

def SpOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (m k : ℕ), 1 ≤ k → (∀ j < m, HL E j) →
    ∀ d : ℕ, 1 ≤ d → ∀ Γ : Matrix (Fin k) (Fin k) E, Γ.det ≠ 0 → FinCl (SplitSet E m k d {Γ})

theorem partSplit_of_one (h : SpOne) : PartSplit := by
  unfold PartSplit
  unfold SpOne at h
  intro F E _ _ _ _ _ _ _ m k hk hHL d hd G hG hdet

  have h1 : ∀ Γ ∈ G, FinCl (SplitSet E m k d {Γ}) := fun Γ hΓ => h E m k hk hHL d hd Γ (hdet Γ hΓ)
  choose T hTfin hT using h1
  refine ⟨⋃ (Γ) (hΓ : Γ ∈ G), T Γ hΓ, hG.biUnion' hTfin, ?_⟩
  rintro p ⟨hpL, v, hv, hvG⟩
  obtain ⟨q, hq, hiso⟩ := hT _ hvG p ⟨hpL, v, hv, Set.mem_singleton _⟩
  exact ⟨q, Set.mem_iUnion₂.mpr ⟨_, hvG, hq⟩, hiso⟩

end PIW.AdelClassFin
