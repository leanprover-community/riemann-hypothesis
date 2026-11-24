module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelProductActionMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.unipotentModelProductAction_measurePreserving : ∀ (E : Type) [Field E] [NumberField E] (k r : ℕ) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E), (∀ w, gM A γ w ∈ Nset k r) → MeasurePreserving (actM A γ) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) := by
  first | exact @GlobalTheory.SnMass.VolN.actM_measurePreserving | exact GlobalTheory.SnMass.VolN.actM_measurePreserving | (intros; apply GlobalTheory.SnMass.VolN.actM_measurePreserving <;> assumption)
