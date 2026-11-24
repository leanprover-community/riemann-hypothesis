module

public import Development.EtaleCohomology.EtaleSheaves.HensCut
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

open Polynomial

namespace LateralTheory.E.MonicSplitsPf

theorem selfDualLattice_projection_mem_of_unit_length (R : Type) [CommRing R] [IsDomain R] (hA : GlobalTheory.EtC.AIC R) :
    ∀ n : ℕ, ∀ p : Polynomial R, p.Monic → p.natDegree = n →
      ∃ s : Multiset R, p = (s.map fun a => X - C a).prod := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    refine ⟨0, ?_⟩
    simpa using hp.natDegree_eq_zero.mp hn
  | succ n ih =>
    intro p hp hn
    obtain ⟨a, ha⟩ := hA p hp (by omega)
    have hroot : IsRoot p a := ha
    have hmul := (mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).mpr hroot
    set q := p /ₘ (X - C a) with hq
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [hmul]; exact hp)
    have hqd : q.natDegree = n := by
      rw [hq, natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C, hn]; omega
    obtain ⟨s, hs⟩ := ih q hqm hqd
    refine ⟨a ::ₘ s, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

theorem MonicSplits_of : LateralTheory.E.HensCut.MonicSplits := by
  intro R _ _ hA p hp
  exact selfDualLattice_projection_mem_of_unit_length R hA p.natDegree p hp rfl

end LateralTheory.E.MonicSplitsPf
