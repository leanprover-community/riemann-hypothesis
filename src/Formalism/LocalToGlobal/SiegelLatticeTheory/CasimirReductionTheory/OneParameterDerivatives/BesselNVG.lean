module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.LitS.PfNVG

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def BesselNVG : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ),
    2 ≤ k → Even k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.IsHCParam u → Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b) → Formalism.MainNotions.CayleySignature.InterlacingCondition k r u v b →
    Formalism.MainNotions.CayleySignature.HalfIntegralDifference k r u v b → Formalism.MainNotions.CayleySignature.GapBig k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Formalism.MainNotions.CayleySignature.Mat k r → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDSHpk k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Formalism.MainNotions.CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), Formalism.MainNotions.S.IsHCTypeW k r z u π →
  ∀ w : H, Formalism.MainNotions.S.IsLowUnitH k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ w →
  ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
  ∃ x x₀ : Formalism.MainNotions.CayleySignature.Mat k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ *
          star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) ≠ 0

end Formalism.L2.SG.LitS.PfNVG
