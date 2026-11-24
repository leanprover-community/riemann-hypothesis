module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.gradedPieceSizes_unipotent_levi_compact_move : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ u m k : I.Ginf, (∀ v, u v ∈ flagN (I.ε v) (flagAt I S v)) → (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) → (∀ v, k v ∈ maxK (I.ε v)) → ∀ i : Fin a, Formalism.HN.sizeQ (bas I) (frm I (u * m * k, xf)) (S i.succ) (S i.castSucc) ^ I.f = Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ I.f * ∏ v, locSize j (flagAt I S v) (uMat (m v)) i := by
  first | exact @GlobalTheory.FlagMeas.SizeMove.size_move | exact GlobalTheory.FlagMeas.SizeMove.size_move | (intros; apply GlobalTheory.FlagMeas.SizeMove.size_move <;> assumption)
