module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.LowStable

theorem X_mul_pderiv_totalDegree_le {σ : Type} (u v : σ) (g : MvPolynomial σ ℂ) :
    (X u * pderiv v g).totalDegree ≤ g.totalDegree := by
  apply GlobalTheory.KFixIrr.LowStable.deg_X_pderiv <;> assumption

theorem omE_mem_restrictTotalDegree {P Q R S : ℕ} (D : ℕ) (u v : Ln P Q R S) (h : linePos u = linePos v)
    (g : Pol P Q R S) (hg : g ∈ restrictTotalDegree (Ln P Q R S) ℂ D) :
    omE u v g ∈ restrictTotalDegree (Ln P Q R S) ℂ D := by
  have hN := (mem_restrictTotalDegree _ _ _).1 hg
  have hXd : ∀ a b : Ln P Q R S, X a * pderiv b g ∈ restrictTotalDegree (Ln P Q R S) ℂ D :=
    fun a b => (mem_restrictTotalDegree _ _ _).2 ((X_mul_pderiv_totalDegree_le a b g).trans hN)
  cases hu : linePos u
  · rw [GlobalTheory.CompactHarm.omE_nn u v hu (h ▸ hu) g]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ (hXd v u)) (Submodule.smul_mem _ _ hg)
  · rw [GlobalTheory.CompactHarm.omE_pp u v hu (h ▸ hu) g]
    exact Submodule.add_mem _ (hXd u v) (Submodule.smul_mem _ _ hg)

theorem fockAct2_apply_eq {P Q R S : ℕ} (Z : Mat R S) (g : Pol P Q R S) :
    fockAct2 P Q R S Z g = ∑ c, ∑ d, Z c d • ∑ a, omE (a, c) (a, d) g := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]

  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have : Matrix.single c d (Z c d) = Z c d • (Eab c d : Mat R S) := by
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply, fockAct2_Eab, LinearMap.sum_apply]

theorem fockAct2_mem_restrictTotalDegree {P Q R S : ℕ} (D : ℕ) (Z : Mat R S) (hZ : IsKC Z)
    (g : Pol P Q R S) (hg : g ∈ restrictTotalDegree (Ln P Q R S) ℂ D) :
    fockAct2 P Q R S Z g ∈ restrictTotalDegree (Ln P Q R S) ℂ D := by
  rw [fockAct2_apply_eq]
  refine Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ => ?_
  by_cases hcd : sameBlock c d
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
    refine omE_mem_restrictTotalDegree D _ _ ?_ g hg
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      first | rfl | exact absurd hcd (by simp [sameBlock])
  · rw [hZ c d hcd, zero_smul]
    exact Submodule.zero_mem _

theorem lowOne_stable : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k →
    x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ Z : Formalism.BasicNotions.TH.Mat R S, Formalism.BasicNotions.TH.IsKC Z →
    ∀ f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k'),
    Formalism.BasicNotions.TH.fockAct2 P Q R S Z f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') := by
  intro P Q R S x k k' _ _ Z hZ f hf
  rw [GlobalTheory.KFixIrr.lowOne, Submodule.mem_inf] at hf ⊢
  refine ⟨?_, fockAct2_mem_restrictTotalDegree _ Z hZ f hf.2⟩
  rw [GlobalTheory.KFixIrr.mem_chiOne] at hf ⊢
  intro X hX
  have hc := LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.2 X Z) f
  rw [Module.End.mul_apply, Module.End.mul_apply] at hc
  rw [hc, hf.1 X hX, map_smul]

end GlobalTheory.LowStable
