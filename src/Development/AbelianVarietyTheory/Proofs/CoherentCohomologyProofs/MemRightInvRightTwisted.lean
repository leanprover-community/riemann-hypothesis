module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.TwistedInverseSubgroups

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]

def leftInvRightTwisted (H : Subgroup G) (γ : G) (T : E →ₗ[ℂ] E) : Submodule ℂ (G → E) where
  carrier := {f | (∀ h ∈ H, ∀ g, f (h * g) = f g) ∧ ∀ g, f (g * γ) = T (f g)}
  add_mem' := by
    rintro f₁ f₂ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    exact ⟨fun h hh g => by simp [a₁ h hh g, a₂ h hh g], fun g => by simp [b₁ g, b₂ g]⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨a, b⟩
    exact ⟨fun h hh g => by simp [a h hh g], fun g => by simp [b g]⟩

variable {H : Subgroup G} {γ : G} {T : E →ₗ[ℂ] E} {f : G → E}

end GlobalTheory.TwistedInverseSubgroups
