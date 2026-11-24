module

public import Formalism.PeriodIntegrals.QuotSetU
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

@[expose] public section

open MeasureTheory Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI PI.QuotSetU

def ModProps {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) (D : Matrix (Fin m) (Fin m) ℂ → ℝ) : Prop :=
  (∀ g ∈ G, 0 < D g) ∧ (∀ a ∈ G, ∀ b ∈ G, D (a * b) = D a * D b) ∧
  (∀ c : Matrix (Fin m) (Fin m) ℂ, IsUnit c → (∀ g, c * g * c⁻¹ ∈ G ↔ g ∈ G) →
      ∀ g ∈ G, D (c * g * c⁻¹) = D g) ∧
  (∀ V ⊆ G, IsCompact V → ∃ M : ℝ, ∀ v ∈ V, D v ≤ M)

def ModExists : Prop :=
  ∀ (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)), IsMatGroup G →
    ∃ D : Matrix (Fin m) (Fin m) ℂ → ℝ, ModProps G D ∧
      ((∀ g ∈ G, D g = 1) → ∀ μ : Measure (MtM m), IsHaarOnM G μ → IsRightInvM G μ)

def UHGroup : Prop := ∀ k r : ℕ, IsMatGroup (UH (Hpk k r))

def SsetSub : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Sset k r z ⊆ UH (Hpk k r)

def SsetGroup : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → IsMatGroup (Sset k r z)

def TrivG : Prop :=
  ∀ (k r : ℕ) (D : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ),
    ModProps (UH (Hpk k r)) D → ∀ g ∈ UH (Hpk k r), D g = 1

def TrivS : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∀ D : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ,
      ModProps (Sset k r z) D → ∀ g ∈ Sset k r z, D g = 1

def PolarUH : Prop :=
  ∀ (k r : ℕ), ∀ g ∈ UH (Hpk k r), ∃ u p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
    u ∈ UH (Hpk k r) ∧ uᴴ * u = 1 ∧ p ∈ UH (Hpk k r) ∧ pᴴ = p ∧ g = u * p

def KCompact : Prop := ∀ k r : ℕ, IsCompact {u | u ∈ UH (Hpk k r) ∧ uᴴ * u = 1}

def UWCompact : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → IsCompact (UWset k r z)

def NGroup : Prop :=
  ∀ k r : ℕ, (1 ∈ Nset k r) ∧ (∀ a ∈ Nset k r, ∀ b ∈ Nset k r, a * b ∈ Nset k r) ∧
    ∀ a ∈ Nset k r, a⁻¹ ∈ Nset k r

def NContract : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → ∀ n ∈ Nset k r, ∀ ε : ℝ, 0 < ε →
    ∃ c : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, IsUnit c ∧
      (∀ g, c * g * c⁻¹ ∈ Sset k r z ↔ g ∈ Sset k r z) ∧ ∀ i j, ‖(c * n * c⁻¹ - 1) i j‖ ≤ ε

end PI.QuotSetU.UnitaryGroupMassFormula

end
