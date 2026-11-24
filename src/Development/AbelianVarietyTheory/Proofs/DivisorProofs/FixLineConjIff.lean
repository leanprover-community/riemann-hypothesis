module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem fixLine_conj_iff {n : Type} [Fintype n] [DecidableEq n] (A B : GL n ℂ) (z : n → ℂ) :
    (∃ c : ℂ, (A : Matrix n n ℂ) *ᵥ z = c • z) ↔
      ∃ c : ℂ, ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
        c • ((B : Matrix n n ℂ) *ᵥ z) := by
  have key : ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
      (B : Matrix n n ℂ) *ᵥ ((A : Matrix n n ℂ) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [key, hc, Matrix.mulVec_smul]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [key, ← Matrix.mulVec_smul] at hc
    have h := congrArg (fun w => ((B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ w) hc
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    rwa [inv_mul_cancel_left] at h

theorem fixL_conj_iff : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y g : grp G β) (z : Fin G.n → ℂ),
    FixL G v β y z ↔ FixL G v β (g * y * g⁻¹) ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  intro p _ G v β y g z
  unfold FixL
  rw [map_mul, map_mul, map_inv]
  exact fixLine_conj_iff _ _ z

end GlobalTheory.LKCx
