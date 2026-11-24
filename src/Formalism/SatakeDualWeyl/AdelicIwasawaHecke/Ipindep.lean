module

public import Formalism.SatakeDualWeyl.Statement
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem mem_stabAt_mul_iff (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) (δ : Γ) :
    δ ∈ stabAt Γ K ((γ : G) * g * κ) ↔ γ⁻¹ * δ * γ ∈ stabAt Γ K g := by
  simp only [stabAt, Set.mem_ofPred_eq]
  have e : ((γ : G) * g * κ)⁻¹ * (δ : G) * ((γ : G) * g * κ) =
      (κ : G)⁻¹ * (g⁻¹ * ((γ⁻¹ * δ * γ : Γ) : G) * g) * κ := by
    push_cast; group
  rw [e, K.mul_mem_cancel_right κ.2, K.mul_mem_cancel_left (K.inv_mem κ.2)]

theorem card_stabAt_mul (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) :
    Nat.card (stabAt Γ K ((γ : G) * g * κ)) = Nat.card (stabAt Γ K g) := by
  refine Nat.card_congr
    { toFun := fun δ => ⟨γ⁻¹ * δ.1 * γ, (mem_stabAt_mul_iff Γ K g γ κ δ.1).1 δ.2⟩
      invFun := fun δ => ⟨γ * δ.1 * γ⁻¹, (mem_stabAt_mul_iff Γ K g γ κ _).2 (by
        convert δ.2 using 2; group)⟩
      left_inv := fun δ => Subtype.ext (by group)
      right_inv := fun δ => Subtype.ext (by group) }

end Formalism.UG.P
