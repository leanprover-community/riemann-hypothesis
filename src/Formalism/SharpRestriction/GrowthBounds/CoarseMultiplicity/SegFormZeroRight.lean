module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem famOK_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {C0 CE1 CE2 Cm : ℝ} {X : Loc}
    [NeZero X.m] {β : GlobalTheory X} {u : Vecs O C0 CE1 CE2 X} (h : FamOK O C0 CE1 CE2 Cm X β u) {j : Fin (numSeg X.TT)}
    (hj : ¬ Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) : u j = 0 := by
  obtain ⟨hL, hz⟩ := h j
  funext b
  by_cases hb : b = β j
  · subst hb
    have hm := (Submodule.mem_pi.mp hL) (β j) (Set.mem_univ _)
    rw [if_neg hj] at hm
    simpa using hm
  · exact hz b hb

theorem segForm_zero_left {O : Type} [CommRing O] [IsDomain O] {p r s : ℕ} (S : SegData s)
    (g : SegVs O r s S.t) : segForm O p r S 0 g = 0 := by
  unfold segForm fock
  simp

end Formalism.MainNotions.ColumnSystems.Pf
