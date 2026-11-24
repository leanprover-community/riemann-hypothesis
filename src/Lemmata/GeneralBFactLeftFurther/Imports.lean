module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Bl.general_b_fact_left_further

theorem goal1 :
  ∀ {n : Nat} {mu : Fin n → Int},
  Formalism.MainNotions.G.Dominant mu → ∀ (c : Int) (m : Fin n), Iff (LE.le.{0} c (mu m)) (LT.lt.{0} m.val (Formalism.MainNotions.G.colH mu c)) := by
  intro n mu hd c m
  have ha : Antitone mu := hd
  unfold Formalism.MainNotions.G.colH
  constructor
  · intro h
    have hsub : Finset.Iic m ⊆ Finset.univ.filter (fun k => c ≤ mu k) := by
      intro k hk
      rw [Finset.mem_Iic] at hk
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ k, le_trans h (ha hk)⟩
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h1
    omega
  · intro h
    by_contra hc
    have hsub : Finset.univ.filter (fun k => c ≤ mu k) ⊆ Finset.Iio m := by
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [Finset.mem_Iio]
      by_contra hkm
      have hmk : m ≤ k := not_lt.mp hkm
      exact hc (le_trans hk.2 (ha hmk))
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h1
    omega

end Bl.general_b_fact_left_further
