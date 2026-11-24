module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SigmaSplitSymmInl
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.Pair

def innerAlgEquiv (R : Type) {A : Type} [CommRing R] [Ring A] [Algebra R A] (y : Aˣ) : A ≃ₐ[R] A :=
  GlobalTheory.InnerAutomorphism.innerAut R y

theorem rel_pol_c : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G), P.Rel Q → Q.pol = P.pol ∧ Q.c = P.c := by
  intro p _ G P Q ⟨y, s, _, hβ, hγ⟩
  refine ⟨?_, ?_⟩
  · have h := minpoly.algEquiv_eq (innerAlgEquiv G.F y) (P.γ : G.C)
    simp only [pol, hγ, Units.val_mul]
    exact h
  · have hsh : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
      intro a b; simp [sh]
    have hy : ∀ X : G.C, sh G (y : G.C) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * X) = X := by
      intro X
      rw [← mul_assoc, ← hsh, Units.inv_mul, sh, map_one, MulOpposite.unop_one, one_mul]
    have core : (y : G.C) * P.γ * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * P.β * sh G y) *
        (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G P.γ * sh G y)) = (P.c : ℚ) • ((y : G.C) * P.β * sh G y) := by
      calc (y : G.C) * P.γ * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * P.β * sh G y) *
            (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G P.γ * sh G y))
          = y * (P.γ * P.β * sh G P.γ) * sh G y := by
            simp only [mul_assoc, Units.inv_mul_cancel_left, hy]
        _ = _ := by
            rw [P.sim, ← Algebra.smul_def]
            simp only [mul_smul_comm, smul_mul_assoc]
    have key : algebraMap ℚ G.C (Q.c : ℚ) * Q.β = algebraMap ℚ G.C (P.c : ℚ) * Q.β := by
      rw [← Q.sim, hγ, hβ]
      simp only [Units.val_mul, hsh, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
      rw [core, smul_comm]
    have hinj : Function.Injective (algebraMap ℚ G.C) := (algebraMap ℚ G.C).injective
    exact Units.ext (hinj ((Units.mul_left_inj Q.β).mp key))

end GlobalTheory.LKMid.Pair
