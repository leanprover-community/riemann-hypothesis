module

public import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne
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

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem norm_for_all_alpha : NormAllAlpha := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm tr hinj hnm htr hadd hlin hadj h2 α α' u hu2 hα hα'
  have symm : ∀ a b, cob φ a b = cob φ b a := by
    intro a b; unfold cob; rw [add_comm a b]; abel
  have add2 : ∀ a b b', cob φ a (b + b') = cob φ a b + cob φ a b' := by
    intro a b b'; rw [symm, hadd, symm b, symm b']
  have e1 : φ ((α + α') • u) = φ (α • u) + φ (α' • u) + cob φ (α • u) (α' • u) := by
    unfold cob; rw [add_smul]; abel
  have e2 : cob φ (α • u) (α' • u) = cob φ u ((star α * α') • u) := by rw [hadj, smul_smul]
  have e3 : cob φ u ((star α * α') • u) + cob φ u ((star α * α') • u)
      = (tr (star α * α')) • cob φ u u := by
    have h : cob φ u ((star α * α') • u) = cob φ u (star (star α * α') • u) := by
      rw [symm, hadj]
    nth_rewrite 1 [h]; rw [← add2, ← add_smul, ← htr, hlin]
  have e4 : cob φ u u = φ u + φ u := by
    unfold cob; rw [← two_smul O u, hu2]
    have : (4 : Z) • φ u = φ u + φ u + φ u + φ u := by
      rw [show (4 : Z) = 1 + 1 + 1 + 1 by norm_num]; simp [add_smul]
    rw [this]; abel
  have e5 : cob φ u ((star α * α') • u) = tr (star α * α') • φ u := by
    apply sub_eq_zero.1; apply h2
    have : ∀ x y : Q, (x - y) + (x - y) = (x + x) - (y + y) := by intro x y; abel
    rw [this, e3, e4, smul_add, sub_self]
  have e6 : nm (α + α') = nm α + nm α' + tr (star α * α') := by
    apply hinj; simp only [map_add (f := _), hnm, htr, star_add, star_mul, star_star]; ring
  rw [e1, e2, e5, hα, hα', e6, add_smul, add_smul]

end Formalism.HermitianLattices.IntegralLatticeDensity
