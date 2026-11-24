module

public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
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
import Formalism.HermitianCurvature.StatementQr

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh


open Matrix in
theorem _root_.GlobalTheory.WigSh.wigMap_zero_of_contraction : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (V₂ →L[ℂ] V₂)) (φ : V₂ →L[ℂ] V₁), (∀ v, ‖φ v‖ ≤ ‖v‖) → (∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, ∀ v, φ (π₂ h v) = π₁ h (φ v)) → _root_.GlobalTheory.WigSh.WigMap k r z π₂ π₁ 0 (fun _ => φ) := by
  intro V₁ _ _ V₂ _ _ k r z π₁ π₂ φ hφ heqv
  refine ⟨⟨1, fun _ => 1, fun _ => φ, fun _ => by simp, fun ω => by simp⟩,
    fun h hh ω => ?_, fun t ω => by simp, fun ω _ _ => ?_⟩
  · ext v
    exact heqv h hh v
  · have hle : ‖φ‖ ≤ 1 := φ.opNorm_le_bound zero_le_one (fun v => by simpa using hφ v)
    rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) hle

end GlobalTheory.WigSh
