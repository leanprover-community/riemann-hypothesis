module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapsLargeGapPeriodIdentities
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

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem _root_.GlobalTheory.T.exists_besselMaps_largeGap_periodIdentities : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → 0 < L.κN → L.κN ≠ ⊤ → ∃ (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), GlobalTheory.AmpTK.BeTK L l l' ∧ GlobalTheory.AmpTK.SmCW L l ∧ GlobalTheory.AmpTK.SmCW L l' := by
  first | exact @GlobalTheory.AmpTKGap.exists_besselTK | exact GlobalTheory.AmpTKGap.exists_besselTK | (intros; apply GlobalTheory.AmpTKGap.exists_besselTK <;> assumption)
