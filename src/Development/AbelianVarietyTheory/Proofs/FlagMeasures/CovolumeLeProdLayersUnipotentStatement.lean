module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeLeProdLayersUnipotent
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.covolume_le_prod_layers_unipotent : ∀ (ι : Type) [Fintype ι] (n d m : ℕ) (ε : ι → Fin n → Bool) (A : ι → ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : ι → Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), (∀ v c, A v (c + 1) ≤ A v c) → (∀ v, A v m = ⊥) → (∀ v c, ∀ X ∈ A v c, ∀ Y ∈ A v 0, X * Y ∈ A v (c + 1) ∧ Y * X ∈ A v (c + 1)) → (∀ v c, ∀ X ∈ A v c, Formalism.REAL.Jm (ε v) * Xᴴ * Formalism.REAL.Jm (ε v) ∈ A v c) → (∀ v i k, ((E v i * (E v k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ v c X, (X ∈ A v c ∧ Formalism.REAL.inG (ε v) X) ↔ X ∈ Submodule.span ℝ (E v '' {i | c ≤ deg i})) → ∀ (ν : ∀ v, Measure (Formalism.REAL.UJ (ε v))) [∀ v, SigmaFinite (ν v)], (∀ v, IsGaugeSub {g | uMat g - 1 ∈ A v 0} d (ν v)) → ∀ (Γ : Subgroup (∀ v, Formalism.REAL.UJ (ε v))) (D : ∀ c : ℕ, Set (ι → {i : Fin d // deg i = c} → ℝ)), (∀ γ ∈ Γ, ∀ v, uMat (γ v) - 1 ∈ A v 0) → (∀ c, MeasurableSet (D c)) → (∀ (c : ℕ) (x : ι → {i : Fin d // deg i = c} → ℝ), ∃ γ ∈ Γ, (∀ v, uMat (γ v) - 1 ∈ A v c) ∧ (fun v (i : {i : Fin d // deg i = c}) => (((uMat (γ v) - 1) * (E v i.1)ᴴ).trace).re + x v i) ∈ D c) → covol (Γ : Set (∀ v, Formalism.REAL.UJ (ε v))) (Measure.pi ν) {g | ∀ v, uMat (g v) - 1 ∈ A v 0} ≤ ∏ c ∈ Finset.range m, volume (D c) := by
  first | exact @GlobalTheory.NilCov.covol_le_prod_layers | exact GlobalTheory.NilCov.covol_le_prod_layers | (intros; apply GlobalTheory.NilCov.covol_le_prod_layers <;> assumption)
