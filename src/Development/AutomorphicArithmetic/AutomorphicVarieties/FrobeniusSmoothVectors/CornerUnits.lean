module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K]

def cor : Fin 2 → Fin 3 := ![0, 2]

theorem w_cor (i : Fin 2) : w 3 (cor i) = w 2 i := by
  fin_cases i <;> rfl

structure IsCorner (ρ : NRep F 3 K) (σ : NRep F 2 K) : Prop where
  odd : ∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0
  r : ∀ g i j, σ.r g i j = ρ.r g (cor i) (cor j)
  ψ : ∀ v i g, σ.ψ v i g = ρ.ψ v (cor i) g
  mid : ∀ v g, ρ.r (F.loc0 v g) 1 1 = ρ.ψ v 1 g

def CornerUnits (ρ : NRep F 3 K) : Prop :=
  ∀ v, ∃ g, IsUnit (ρ.r (F.loc0 v g) 1 1 - ρ.ψ v 0 g) ∧ IsUnit (ρ.r (F.loc0 v g) 1 1 - ρ.ψ v 2 g) ∧
    IsUnit ((ρ.r (F.loc0 v g) 0 0 - ρ.ψ v 1 g) * (ρ.r (F.loc0 v g) 2 2 - ρ.ψ v 1 g) -
      ρ.r (F.loc0 v g) 0 2 * ρ.r (F.loc0 v g) 2 0)

theorem mid_mul (ρ : NRep F 3 K) (h : ∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0) (g g' : F.G0) :
    ρ.r (g * g') 1 1 = ρ.r g 1 1 * ρ.r g' 1 1 := by
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, h g 1 0 (by decide), h g 1 2 (by decide)]
  simp

end UpperTheory.V.Fr
