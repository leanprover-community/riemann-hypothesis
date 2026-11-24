module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePiPointsAtInfinitePlacesCMTypeImage
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.measurePi_pointsAtInfinitePlacesCMType_image : ∀ (D : D7) (S : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)), Measure.pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (Gm D '' S) = Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) S := by
  first | exact @GlobalTheory.CovDom.measure_Gm_image | exact GlobalTheory.CovDom.measure_Gm_image | (intros; apply GlobalTheory.CovDom.measure_Gm_image <;> assumption)
