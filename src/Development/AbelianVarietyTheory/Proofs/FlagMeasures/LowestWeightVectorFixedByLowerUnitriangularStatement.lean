module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestWeightVectorFixedByLowerUnitriangular
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.lowest_weight_vector_fixed_by_lower_unitriangular : ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), Formalism.QuantumDeterminants.IsCRepOn (GlobalTheory.Dec.KC ε) τ → DifferentiableAt ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) (fun i j => (1 : Matrix (Fin n) (Fin n) ℂ) i j) → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) τ (-abelian₂) w → (∀ (μ : Fin n → ℝ) (v : W), v ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) τ (-μ) v → Formalism.MainNotions.S.CDom ε μ abelian₂) → ∀ y ∈ GlobalTheory.Dec.KC ε, Formalism.MainNotions.S.IsLoUni y → τ y w = w := by
  first | exact @GlobalTheory.Dec.LowFix.lowest_fixed | exact GlobalTheory.Dec.LowFix.lowest_fixed | (intros; apply GlobalTheory.Dec.LowFix.lowest_fixed <;> assumption)
