module

public import Formalism.SatakeDualWeyl.Statement
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MonomialSign

theorem diagonal_mul_eq {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hcard : Fintype.card κ = Fintype.card ι) (ε : ι → ℝ) (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    (M : Matrix ι κ ℂ) (d : κ → ℝ) (hd : ∀ i, d i ≠ 0)
    (hM : Mᴴ * Matrix.diagonal (fun a => (ε a : ℂ)) * M = Matrix.diagonal (fun i => (d i : ℂ)))
    (hrow : ∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) :
    Matrix.diagonal (fun a => (ε a : ℂ)) * M
      = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  have hsum : ∀ i, d i = ∑ a, ε a * Complex.normSq (M a i) := by
    intro i
    have h := congrFun (congrFun hM i) i
    rw [Matrix.diagonal_apply_eq, Matrix.mul_apply] at h
    apply Complex.ofReal_injective
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self,
      Complex.star_def]
    ring
  have hex : ∀ i, ∃ a, M a i ≠ 0 := by
    intro i
    by_contra hne
    push Not at hne
    apply hd i
    rw [hsum i]
    simp [hne]
  choose r hr using hex
  have hinj : Function.Injective r := fun i j hij => hrow (r i) i j (hr i) (hij ▸ hr j)
  have hbij : Function.Bijective r :=
    (Fintype.bijective_iff_injective_and_card r).2 ⟨hinj, hcard⟩
  have huniq : ∀ a i, M a i ≠ 0 → a = r i := by
    intro a i h
    obtain ⟨j, rfl⟩ := hbij.2 a
    rw [hrow (r j) i j h (hr j)]
  ext a i
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : M a i = 0
  · simp [h]
  · have ha := huniq a i h
    have hdi : d i = ε a * Complex.normSq (M a i) := by
      rw [hsum i]
      refine Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)
      have : M b i = 0 := by
        by_contra hb'
        exact hb ((huniq b i hb').trans ha.symm)
      simp [this]
    have hpos : 0 < Complex.normSq (M a i) := Complex.normSq_pos.2 h
    rcases hε a with h1 | h1
    · have : 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]
    · have : ¬ 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]

theorem Jpq_mul_eq : ∀ (n p q : ℕ), p + q = n → ∀ (M : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (d : Fin n → ℝ), (∀ i, d i ≠ 0) → Mᴴ * Formalism.UG.Jpq p q * M = Matrix.diagonal (fun i => (d i : ℂ)) → (∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) → Formalism.UG.Jpq p q * M = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  intro n p q hn M d hd hM hrow
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal
      (fun a => ((Sum.elim (fun _ => 1) (fun _ => -1) a : ℝ) : ℂ)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hJ] at hM ⊢
  refine diagonal_mul_eq (by simp [hn]) _ ?_ M d hd hM hrow
  rintro (a | a) <;> simp

end GlobalTheory.MonomialSign
