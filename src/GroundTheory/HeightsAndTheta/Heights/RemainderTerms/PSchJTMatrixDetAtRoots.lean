module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem SchJTMatrixDetAtRoots.proof (h1 : SchRootOfUnityBialternant.Statement)
    (h2 : SchRootOfUnityRowsPerm.Statement) (h3 : SchRootOfUnityRowsEq.Statement)
    (h4 : SchHookResidues.Statement) (h5 : SchNonHookResidues.Statement)
    (h6 : SchRootOfUnityVandermondeNe.Statement) : SchJTMatrixDetAtRoots.Statement := by
  intro k nu hk hanti hsum
  have hV := h6 k hk
  have hB := h1 k nu hk

  have hstair : (Matrix.of fun i j : Fin k =>
      rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).det =
      vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := by
    rw [← Schur.det_pow_staircase_eq_vandermondeOf (fun j : Fin k => rootOfUnity k ^ (j : ℕ))]
    congr 1
    ext i j
    simp [Matrix.of_apply, pow_mul]
  split_ifs with hhook
  · obtain ⟨π, hres, hsign⟩ := h4 k nu hk hanti hsum hhook
    have hP := h2 k (fun i => nu i + (k - 1 - (i : ℕ))) π hk hres
    rw [hstair] at hP
    have hP' : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
          vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := hP
    rw [hB] at hP'
    have := mul_right_cancel₀ hV hP'
    rw [this, hsign]
    push_cast
    rfl
  · obtain ⟨i, i', hne, hres⟩ := h5 k nu hk hanti hsum hhook
    have hZ : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det = 0 :=
      h3 k (fun i => nu i + (k - 1 - (i : ℕ))) i i' hne hres
    rw [hB] at hZ
    exact (mul_eq_zero.mp hZ).resolve_right hV

end GroundTheory.Heights₂.Heights.RestTerms
