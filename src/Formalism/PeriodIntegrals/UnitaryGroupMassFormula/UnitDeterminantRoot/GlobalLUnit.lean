module

public import Formalism.PeriodIntegrals.UnitDetRoot
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

abbrev KF (b : ℤ) (d : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({UnitDetRootDefs.cmTheta b d} : Set ℂ)

def IsLUnit (l : ℕ) (x : ℂ) : Prop :=
  x ≠ 0 ∧ ∃ k : ℕ, ¬ l ∣ k ∧ IsIntegral ℤ ((k : ℂ) * x) ∧ IsIntegral ℤ ((k : ℂ) * x⁻¹)

def Hyp (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)) : Prop :=
  UnitDetRootDefs.CmOK a b c d ∧ UnitDetRootDefs.IsSelfDual (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa ∧
    (∀ x ∈ Λa, UnitDetRootDefs.cmTheta b d • x ∈ Λa) ∧
    UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa ≠ 0 ∧
    UnitDetRootDefs.relIdx Λa (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0

def admitted (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ))
    (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) : Prop :=
  UnitDetRootDefs.IsIsom (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m)
      (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
    UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
    UnitDetRootDefs.relIdx (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0

def EqAway {V : Type*} [AddCommGroup V] [Module ℂ V] (l : ℕ) (Λ Λ' : AddSubgroup V) : Prop :=
  ∃ k : ℕ, ¬ l ∣ k ∧ (∀ x ∈ Λ, (k : ℂ) • x ∈ Λ') ∧ (∀ x ∈ Λ', (k : ℂ) • x ∈ Λ)

def DetInK : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
    Hyp a b c d ha hd lam hlam m Λa → ∀ δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ), admitted a b d ha hd lam hlam m Λa δ →
      LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∈ KF b d ∧
      LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) * conj (LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))) = 1

def LocalStd : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
    Hyp a b c d ha hd lam hlam m Λa → ∀ (l : ℕ) [Fact l.Prime] (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)),
      admitted a b d ha hd lam hlam m Λa δ →
      ¬ l ∣ UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
      EqAway l (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa)

def GlobalLUnit : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
    Hyp a b c d ha hd lam hlam m Λa → ∃ γ : ℂ, γ ∈ KF b d ∧ γ ≠ 0 ∧ ∃ n : ℕ, 0 < n ∧
      ∀ (l : ℕ) [Fact l.Prime] (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)), admitted a b d ha hd lam hlam m Λa δ →
        EqAway l (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
        IsLUnit l (γ / LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ^ n)

def NormOne : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (x : ℂ), IsLUnit l x → ‖ι x‖ = 1

def RootStep : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ), UnitDetRootDefs.CmOK a b c d → ∀ β ∈ KF b d, β * conj β = 1 → ∀ N : ℕ, 0 < N →
    ∃ κ : ℂ, κ ^ N = β⁻¹ ∧ IsAlgebraic ℚ κ ∧ ∀ σ : ℂ ≃+* ℂ, ‖σ κ‖ = 1

def ConjMem : Prop := ∀ (b : ℤ) (d : ℕ) (x : ℂ), x ∈ KF b d → conj x ∈ KF b d

def ConjLUnit : Prop := ∀ (l : ℕ) (x : ℂ), IsLUnit l x → IsLUnit l (conj x)

end PI.UnitaryGroupMassFormula.UnitDetRoot
