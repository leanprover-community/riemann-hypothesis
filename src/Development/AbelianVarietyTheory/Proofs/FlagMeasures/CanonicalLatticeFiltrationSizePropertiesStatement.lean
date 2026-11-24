module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
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

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

theorem _root_.GlobalTheory.T.canonicalLatticeFiltration_size_properties : ∀ (I : AutInst) (x : I.GA) (t : ℝ), 0 < t → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLe I x t) ∧ IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLt I x t) ∧ stepLt I x t ≤ stepLe I x t ∧ (∀ t', t < t' → stepLe I x t ≤ stepLt I x t') ∧ (stepLe I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLe I x t) ≤ t) ∧ (stepLt I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLt I x t) < t) ∧ (∀ N, stepLe I x t < N → N ≤ lamX I x → t < sizeQ (bas I) (frm I x) N (stepLe I x t)) ∧ (∀ N, stepLt I x t < N → N ≤ lamX I x → t ≤ sizeQ (bas I) (frm I x) N (stepLt I x t)) ∧ (1 ≤ I.n → 0 < least I x ∧ (stepLe I x t = ⊥ ↔ t < least I x) ∧ (stepLt I x t = ⊥ ↔ t ≤ least I x)) := by
  first | exact @GlobalTheory.CountSteps.steps | exact GlobalTheory.CountSteps.steps | (intros; apply GlobalTheory.CountSteps.steps <;> assumption)
