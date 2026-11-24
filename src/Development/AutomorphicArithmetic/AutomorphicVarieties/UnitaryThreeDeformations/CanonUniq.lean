module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
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
import Mathlib.Tactic.Basify
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

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem canon_eig {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R)
    (h : GL (Fin 3) R) (hc : Canon X h) :
    ∃ d : Fin 3 → R, ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h = diagonal d ∧
      ∀ a, d a - X a a ∈ maximalIdeal R := by
  let φ := residue R
  have h0 : φ.mapMatrix (h.val - 1) = 0 := by
    ext a b
    exact (residue_eq_zero_iff _).2 (hc.hat a b)
  have hh : φ.mapMatrix h.val = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0
  have hhi : φ.mapMatrix h⁻¹.val = 1 := by
    have e : φ.mapMatrix h⁻¹.val * φ.mapMatrix h.val = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    rwa [hh, mul_one] at e
  refine ⟨fun a => (h⁻¹.val * X * h.val) a a, hc.diag.diagonal_diag.symm, ?_⟩
  intro a
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
  have e : φ.mapMatrix (h⁻¹.val * X * h.val) = φ.mapMatrix X := by
    rw [map_mul, map_mul, hh, hhi, one_mul, mul_one]
  exact congrFun (congrFun e a) a

theorem UpperTheory.V.UnitaryThreeInertia.canon_unique :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R) (h h' : GL (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → Canon X h → Canon X h' → h = h' := by
  intro R _ _ X h h' hX hc hc'
  obtain ⟨d, hd, hdX⟩ := canon_eig X h hc
  obtain ⟨d', hd', hd'X⟩ := canon_eig X h' hc'
  let g : GL (Fin 3) R := h⁻¹ * h'
  have key : diagonal d * g.val = g.val * diagonal d' := by
    rw [← hd, ← hd']
    simp only [g, Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  have hg : ∀ a b, a ≠ b → g.val a b = 0 := by
    intro a b hab
    have e := congrFun (congrFun key a) b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    have hu : IsUnit (d a - d' b) := by
      by_contra hn
      have hm : d a - d' b ∈ maximalIdeal R := hn
      have hm2 : X a a - X b b ∈ maximalIdeal R := by
        have e2 : X a a - X b b = (d a - d' b) - (d a - X a a) + (d' b - X b b) := by ring
        rw [e2]
        exact add_mem (sub_mem hm (hdX a)) (hd'X b)
      exact hm2 (hX a b hab)
    have e3 : g.val a b * (d a - d' b) = 0 := by
      rw [mul_sub, mul_comm (g.val a b) (d a), e, sub_self]
    exact hu.mul_left_eq_zero.1 e3
  have hh' : h'.val = h.val * g.val := by
    simp only [g, Units.val_mul, Units.mul_inv_cancel_left]
  have g1 : g.val = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq]
      have e := congrFun (congrFun hh' a) a
      rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hg c a hc, mul_zero])
        (by simp), hc'.one a, hc.one a, one_mul] at e
      exact e.symm
    · rw [Matrix.one_apply_ne hab, hg a b hab]
  have g1' : g = 1 := Units.ext g1
  exact inv_mul_eq_one.1 g1'
