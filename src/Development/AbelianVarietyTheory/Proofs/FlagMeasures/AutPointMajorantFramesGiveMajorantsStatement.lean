module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
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

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

theorem _root_.GlobalTheory.T.autPointMajorantFrames_give_majorants : ∀ (I : AutInst) (x : I.GA), IsTotallyComplex I.E ∧ nPl I.E = I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) ∧ ∀ w : InfinitePlace I.E, IsUnit (frm I x w).det ∧ (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Jm (I.ε (w.comap (algebraMap I.F I.E))) ∧ (∀ y z : (Fin I.n → I.E), ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤ Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z) ∧ ∀ k : I.GA, (∀ v, uMat (k.1 v) ∈ Kset (I.ε v)) → ∀ y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  first | exact @GlobalTheory.Count.FrameMajorant.frames_give_majorants | exact GlobalTheory.Count.FrameMajorant.frames_give_majorants | (intros; apply GlobalTheory.Count.FrameMajorant.frames_give_majorants <;> assumption)
