module

public import Development.EtaleCohomology.EtaleTrace.LPdCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LEmptyPf

theorem sec_subsingleton {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (F : Shv R) :
    Subsingleton (Sec F X) := by
  have ht : IsTerminal (F.obj.obj (Opposite.op X)) :=
    Sheaf.isTerminalOfBotCover F X (by exact Scheme.bot_mem_grothendieckTopology X)
  have hz : IsZero (F.obj.obj (Opposite.op X)) := ht.isZero
  exact ModuleCat.subsingleton_of_isZero hz

theorem pos_zero (a5 : A5) {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (F : Shv R) (n : ℤ)
    (hn : 0 < n) (x : H R (sch.obj X) F n) : x = 0 := by
  obtain ⟨Y, f, -, -, hx⟩ := a5 R X F n hn x
  have : IsEmpty Y := Function.isEmpty f.base
  have : IsIso f := isIso_of_isEmpty f
  have h1 : x = pull R (sch.map (inv f)) F n (pull R (sch.map f) F n x) := by
    rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  rw [h1, hx, map_zero]

theorem LEmpty_of : LateralTheory.EtaleTrace.LPdCut.LEmpty := by
  intro a5 a9 R _ X hX F n
  refine ⟨fun a b => ?_⟩
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact ((a9 R F).1 _ n h).elim a b
  · obtain ⟨e, -⟩ := (a9 R F).2
    have := sec_subsingleton X F
    exact (e X).symm.injective (Subsingleton.elim _ _)
  · rw [pos_zero a5 X F n h a, pos_zero a5 X F n h b]

end LateralTheory.EtaleTrace.LEmptyPf
