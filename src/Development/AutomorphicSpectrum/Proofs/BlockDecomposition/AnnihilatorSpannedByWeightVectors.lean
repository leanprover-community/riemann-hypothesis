module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.EigenvectorsSumZeroEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho

theorem eq_zero_of_sum_weightVec {ι κ A : Type} [DecidableEq ι] [AddCommGroup A] [Module ℂ A]
    (T : κ → Module.End ℂ A) (f : ι → κ → ℂ) (hf : Function.Injective f) (s : Finset ι) :
    ∀ v : ι → A, (∀ i ∈ s, ∀ k, T k (v i) = f i k • v i) → ∑ i ∈ s, v i = 0 →
      ∀ i ∈ s, v i = 0 :=
  _root_.UpperTheory.Reformulated.B.P6.r14a.GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec T f hf s

def wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : U n :=
  ∑ m ∈ (pbw.repr x).support.filter (fun m => wt m = w), pbw.repr x m • canon m

theorem isAdW_wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : IsAdW w (wtPart x w) := by
  intro k
  simp only [wtPart, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub,
    (Finset.mem_filter.1 hm).2, smul_comm]

theorem sum_wtPart {n : ℕ} (x : U n) :
    ∑ w ∈ (pbw.repr x).support.image wt, wtPart x w = x := by
  simp only [wtPart]
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact sum_repr_canon x

theorem mem_span_isAdW_of_kills {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (x : U n) (hx : φ x t = 0) :
    x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  classical
  have hinj : Function.Injective (fun (w : Fin n → ℤ) (k : Fin n) => rhoVec n k + (w k : ℂ)) := by
    intro w w' h
    funext k
    have := congrFun h k
    simpa using this
  have hz := eq_zero_of_sum_weightVec (fun k : Fin n => φ (e (k, k)))
    (fun (w : Fin n → ℤ) k => rhoVec n k + (w k : ℂ)) hinj ((pbw.repr x).support.image wt)
    (fun w => φ (wtPart x w) t)
    (fun w _ k => by
      have h1 : e (k, k) * wtPart x w = wtPart x w * e (k, k) + (w k : ℂ) • wtPart x w := by
        rw [← isAdW_wtPart x w k]; abel
      have h2 := congrArg (fun u => φ u t) h1
      simp only [map_mul, map_add (f := _), map_smul, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.smul_apply, hd k, add_smul] at h2 ⊢
      rw [h2])
    (by
      have h3 := congrArg (fun u => φ u t) (sum_wtPart x)

      simp only [map_sum, LinearMap.sum_apply] at h3
      rw [h3, hx])
  rw [← sum_wtPart x]
  exact Submodule.sum_mem _ fun w hw => Submodule.subset_span ⟨w, isAdW_wtPart x w, hz w hw⟩

end GlobalTheory.CompanionTheory.PresRho
