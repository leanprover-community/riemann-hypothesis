module

public import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem ro_le_arc_len : ∀ {n : ℕ} (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n),
    Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c ≤ A.len c := by
  intro n A c
  unfold Formalism.MainNotions.LocalTheoryWindows.ro Formalism.MainNotions.LocalTheoryWindows.thickLv
  exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem arc_len_le_one_of_no_thick : ∀ {n : ℕ} [NeZero n] (b w S η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ)
    (h : ¬ ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) (c : ZMod n),
    (arcOf b w S η up size).len c ≤ 1 := by
  intro n _ b w S η up size h c
  unfold arcOf
  dsimp only
  refine Nat.sInf_le ?_
  rw [Set.mem_ofPred_eq]
  exact ⟨le_rfl, fun ht => h ⟨_, ht⟩⟩

end Formalism.MainNotions.N.Ln17
