module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

open UpperTheory.V.Af

def Bridge : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (k m n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ m)], 3 ≤ k → Odd k → 1 ≤ m → ∀ (h : m ≤ n)
    (ζ : K), IsPrimitiveRoot ζ (l ^ n) → ∀ ψ : DirichletCharacter K (l ^ m), ψ.IsPrimitive →
    ∀ (b₁ b₂ u v : ℤ → K) (f₁ f₂ : ZMod (l ^ n) → K) (c d : (ZMod (l ^ n))ˣ),
      (∀ x : ℤ, b₁ ((l : ℤ) ^ (n - m) * x) = u x) → (∀ x : ℤ, b₂ ((l : ℤ) ^ (n - m) * x) = v x) →
      (∀ x, u (-x) = ψ (-1) * u x) → (∀ x, v (-x) = -ψ (-1) * v x) → ∀ s : ℕ,
      -((l : K) ^ (n * k) / (l : K) ^ (n * 4)) *
        ∑ γ : ((ZMod (l ^ n))ˣ × (ZMod (l ^ n))ˣ) × ZMod (l ^ n) × ZMod (l ^ n),
          ψ ((((γ.1.1 : ZMod (l ^ n)) * γ.2.2 - (γ.1.2 : ZMod (l ^ n)) * γ.2.1).val : ℕ) : ZMod (l ^ m)) *
            mul (Fser (k - 1) (l ^ n) ζ b₁ (f₁ (c * γ.1.1)) (c * γ.1.1) (c * γ.2.1))
              (Fser 1 (l ^ n) ζ b₂ (f₂ (d * γ.1.2)) (d * γ.1.2) (d * γ.2.2)) s =
      if l ^ n ∣ s then -4 * ((l : K) ^ m)⁻¹ * (∑ a : ZMod (l ^ m), ψ a * ζ ^ (l ^ (n - m) * a.val)) *
        ψ⁻¹ ((((c * d : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val : ℕ) : ZMod (l ^ m)) *
          (Uo l)^[m] (Zs k l u v (quo ψ)) (s / l ^ n) else 0

end GlobalTheory.EisM

end
