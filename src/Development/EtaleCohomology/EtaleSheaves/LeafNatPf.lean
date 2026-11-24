module

public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2

theorem pull_cast_nat {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn hi; rfl

abbrev PB.over {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) : PB (f ≫ V) ⟶ PB V :=
  pullback.map (f ≫ V) (PGL.pr N) V (PGL.pr N) f (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem PB.over_pr {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) :
    PB.over f V ≫ PB.pr V = PB.pr (f ≫ V) ≫ f := by
  simp only [PB.over, PB.pr, pullback.map, pullback.lift_fst]

theorem PB.over_line {E E' : Spc} (f : E ⟶ E') {N : ℕ} (V : E' ⟶ ofCat (glCat N)) :
    PB.over f V ≫ PB.line V = PB.line (f ≫ V) := by
  simp only [PB.over, PB.line, pullback.map, pullback.lift_snd_assoc, Category.comp_id]

theorem LeafNat_of (hA : LeafA6nat) : LeafNat := by
  intro q _ P E E' f h h' N V c hc
  obtain ⟨h0, hz, hs⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · rw [← P.map_ι f h h', h0, map_one]
  · intro j hj; simp [hz j hj]
  · have hg := congrArg (P.map (PB.over f V) (inv_of (PB.pr (f ≫ V)) h) (inv_of (PB.pr V) h')) hs

    rw [map_zero, map_sum] at hg
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, map_pow, P.map_ι, Collected.deg1, pull_cast_nat, ← pull_comp, PB.over_pr]
    rw [(hA q).2.2.1 _ _ (inv_of (PB.pr V) h'), PB.over_line]

end LateralTheory.E.D2
