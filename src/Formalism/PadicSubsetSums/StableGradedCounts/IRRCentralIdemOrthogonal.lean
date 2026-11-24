module

public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdempotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem central_idempotents_orthogonal : CentralIdemOrthogonal := by
  intro G V W _ _ _ _ _ _ _ _ _ _ ρ σ hρ hσ hne
  obtain ⟨μ, h1, h2⟩ := centralIdem_mul ρ σ hσ
  have hirrρ : ρ.IsIrreducible := isIrreducible_of ρ hρ
  have hirrσ : σ.IsIrreducible := isIrreducible_of σ hσ
  have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hno : ¬ Nonempty (Representation.Equiv ρ σ) := by
    rintro ⟨φ⟩
    exact hne ⟨φ.toLinearEquiv, fun g x => LinearMap.congr_fun (φ.isIntertwining' g) x⟩
  have horth := Representation.char_orthonormal σ ρ
  rw [if_neg hno, Nat.card_eq_fintype_card] at horth
  have h3 : ∑ g, ρ.character g⁻¹ * σ.character g = 0 := by
    have e : ∑ g, ρ.character g⁻¹ * σ.character g = ∑ g, σ.character g * ρ.character g⁻¹ :=
      Finset.sum_congr rfl fun g _ => mul_comm _ _
    rw [e]
    simpa using horth
  rw [h3] at h1
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  have hμ : μ = 0 := (mul_eq_zero.mp h1).resolve_right hd
  rw [h2, hμ, mul_zero, zero_smul]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
