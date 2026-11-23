module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingRearrangePiProdMeasures
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.measurePreserving_rearrange_pi_prod_measures : ∀ (V V' V'' : Type) [Fintype V] [Fintype V'] [Fintype V''] (β : V ≃ V') (σ : V ≃ V'') (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (Y : V'' → Type) [∀ w, MeasurableSpace (Y w)] (m : ∀ i, Measure (X i)) [∀ i, SigmaFinite (m i)] (ν : ∀ w, Measure (Y w)) [∀ w, SigmaFinite (ν w)] (b : Fin a → ℝ) (c : V'' → ℝ), (∀ i, 0 ≤ b i) → (∀ w, 0 ≤ c w) → MeasurePreserving (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) (((∏ i, ENNReal.ofReal (b i ^ Fintype.card V)) * ENNReal.ofReal (∏ w, c w)) • (Measure.pi fun i => Measure.pi fun _ : V' => m i).prod (Measure.pi ν)) (Measure.pi fun v : V => (Measure.pi fun i => ENNReal.ofReal (b i) • m i).prod (ENNReal.ofReal (c (σ v)) • ν (σ v))) := by
  first | exact @GlobalTheory.LeviIso.measurePreserving_rearrange | exact GlobalTheory.LeviIso.measurePreserving_rearrange | (intros; apply GlobalTheory.LeviIso.measurePreserving_rearrange <;> assumption)
