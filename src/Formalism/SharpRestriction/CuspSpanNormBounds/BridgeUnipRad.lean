module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
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
public import Formalism.LocalRingCardinality.DataLevel

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeUnipRad

open MeasureTheory NumberField Matrix
open Formalism.MainNotions.S

section CM

variable (I : AutInst)

theorem emb_star (v : InfinitePlace I.F) (x : I.E) : I.φ v (star x) = starRingEnd ℂ (I.φ v x) := by
  obtain ⟨hcm, -, -, -⟩ := I.cm
  unfold Formalism.HermitianLatticesTheory.IsCMUnram at hcm
  exact hcm.2.1 (I.φ v) x

end CM

section Form

variable {n : ℕ}

theorem hform_eq (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  rw [Formalism.UG.hform.eq_1]
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

end Form

section Span

variable (I : AutInst)

end Span

section Rad

variable {n : ℕ}

variable {J' : Matrix (Fin n) (Fin n) ℂ} {U : Submodule ℂ (Fin n → ℂ)}

end Rad

section Sub

variable {n : ℕ} (ε : Fin n → Bool) {P J' : Matrix (Fin n) (Fin n) ℂ}

end Sub

end Formalism.MainNotions.BridgeUnipRad

end
