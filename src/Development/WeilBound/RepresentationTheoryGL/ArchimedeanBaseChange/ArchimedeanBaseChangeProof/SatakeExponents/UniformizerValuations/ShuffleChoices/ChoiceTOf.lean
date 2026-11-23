module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Choice
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail

namespace PositivityTheory.Rg.BcB.F.Choice

theorem choiceTOf : ChoiceTOf := by
  intro hP hC _hG E _ _ _ n w ι _ s Z α hZ
  have hfin : (⋃ i, (fun p : (Fin (s i).a → ℂˣ) × (Fin (s i).b → ℂˣ) => chiOf w (s i) p.1 p.2) '' Z i).Finite :=
    Set.finite_iUnion (fun i => (hZ i).image _)
  obtain ⟨c, hc, h1, h0⟩ := hP n 2 α (hfin.toFinset.erase α) (by simp)
  refine ⟨c, hc, h1, ?_⟩
  intro i p hp hne
  by_contra hneq
  apply hne
  have key : (c.sum fun x a => a * ↑(∏ k : Fin n, (s i).eps k ^ x k) * ev2 w p.1 p.2 (resL (s i) x) (resR (s i) x))
      = evalGL c (chiOf w (s i) p.1 p.2) := by
    unfold evalGL
    refine Finsupp.sum_congr (fun x _ => ?_)
    rw [mul_assoc, hC E n w (s i) p.1 p.2 x]
  rw [key]
  apply h0
  simp only [Finset.mem_erase, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_image]
  exact ⟨hneq, i, p, hp, rfl⟩

end PositivityTheory.Rg.BcB.F.Choice

end
