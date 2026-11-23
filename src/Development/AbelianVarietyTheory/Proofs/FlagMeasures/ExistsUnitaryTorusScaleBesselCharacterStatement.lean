module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_unitaryTorus_scale_besselCharacter : ∀ (k r : ℕ) (c : ℂ), c ≠ 0 → ∃ t ∈ GG k r, (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) ∧ (∀ z, inWb k r z → t *ᵥ z = z ∧ (∀ h ∈ UWset k r z, t * h = h * t) ∧ ∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) ∧ ∀ a : Fin (r + 1), ∃ s : ℂ, s ≠ 0 ∧ ‖s‖ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ‖s‖⁻¹ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ∀ z, inWb k r z → t⁻¹ *ᵥ fvec k r z a = s • fvec k r z a := by
  first | exact @GlobalTheory.TorusScale.exists_torus_scale | exact GlobalTheory.TorusScale.exists_torus_scale | (intros; apply GlobalTheory.TorusScale.exists_torus_scale <;> assumption)
