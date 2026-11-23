module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
public import Formalism.SharpRestriction.CuspSpanNormBounds.ContinuousCjIT
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFiniteCoefAndTorusTranslateIsBesselCoefLargeGap
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

theorem _root_.GlobalTheory.T.kFiniteCoef_and_torusTranslate_isBesselCoef_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), Formalism.MainNotions.S.IsKFinCoefH L.σ f → (∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' f s) ∧ ∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s := by
  first | exact @GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate | exact GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate | (intros; apply GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate <;> assumption)
