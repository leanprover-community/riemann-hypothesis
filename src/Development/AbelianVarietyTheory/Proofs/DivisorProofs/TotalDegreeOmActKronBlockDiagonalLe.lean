module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockBlockDeg

theorem Jm_apply_of_ne {r s : ℕ} {c e : Ix r s} (h : c ≠ e) : Jm r s c e = 0 := by
  rcases c with c | c <;> rcases e with e | e <;>
    simp_all [Jm, Formalism.UG.Jpq]

theorem totalDegree_omAct_kron_le : ∀ (p q r s : ℕ) (E : Mat p q), IsKC E → ∀ (d : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → (omAct p q r s (Matrix.kroneckerMap (· * ·) E (Jm r s)) P).totalDegree ≤ d := by
  intro p q r s E hE d P hP
  rw [← mem_restrictTotalDegree] at hP ⊢
  refine GlobalTheory.FockPolGK.omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change E a b * Jm r s c e = 0
  by_cases hc : c = e
  · subst hc
    rw [hE a b, zero_mul]
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [linePos, sameBlock]
  · rw [Jm_apply_of_ne hc, mul_zero]

end GlobalTheory.FockBlockDeg
