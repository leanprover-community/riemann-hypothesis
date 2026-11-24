module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubquotientCoveringRadiusRealPlaces
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

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.subquotient_covering_radius_real_places : ∀ (I : AutInst) (x : I.GA) (A S R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi : ℝ), A.FG → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ sizeQ (bas I) (frm I x) N S) → largestSize (bas I) (frm I x) R ≤ hi → ∀ T : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, ∀ y ∈ S, T v *ᵥ (fun i => I.φ v (y i)) = 0) → (∀ v, ∀ y ∈ A, T v *ᵥ (fun i => I.φ v (y i)) ∈ spanAt I R v) → ∃ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ S, Φ *ᵥ y = 0) ∧ (∀ y ∈ A, Φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, ∀ u ∈ spanAt I A v, D v *ᵥ u = (T v - Φ.map (I.φ v)) *ᵥ u) ∧ normAt I x D ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt I.f * I.rd * hi / (2 * lo) := by
  first | exact @GlobalTheory.Count.SubquotFrame.subquot_frame | exact GlobalTheory.Count.SubquotFrame.subquot_frame | (intros; apply GlobalTheory.Count.SubquotFrame.subquot_frame <;> assumption)
