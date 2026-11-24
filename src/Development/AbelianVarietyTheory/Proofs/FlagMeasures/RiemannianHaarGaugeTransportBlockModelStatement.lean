module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeTransportBlockModel
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
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.riemannianHaarGauge_transport_block_model : ∀ (n : ℕ) (ε : Fin n → Bool) (c : ℝ) (P Q : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin n) (hf : Sorts ε f), GlobalTheory.Count.IsGauge ε c → 0 < c ∧ HasEuclDensity ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) := by
  first | exact @GlobalTheory.GaugeQuot.gauge_transport | exact GlobalTheory.GaugeQuot.gauge_transport | (intros; apply GlobalTheory.GaugeQuot.gauge_transport <;> assumption)
