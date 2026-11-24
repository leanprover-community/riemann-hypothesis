module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

namespace GlobalTheory.CompanionTheory.RgTransport

theorem exists_joint_kernel_finset {V : Type} [AddCommGroup V] [Module ℂ V]
    (I : Submodule ℂ V) (hI : I ≠ ⊥) (D : ℂ → Module.End ℂ V)
    (hcomm : ∀ Y Y', Commute (D Y) (D Y'))
    (hstab : ∀ Y, ∀ x ∈ I, D Y x ∈ I)
    (hnil : ∀ Y, ∀ x ∈ I, ∃ N : ℕ, (D Y ^ N) x = 0) (F : Finset ℂ) :
    ∃ w ∈ I, w ≠ 0 ∧ ∀ Y ∈ F, D Y w = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff I).1 hI
    exact ⟨x, hx, hx0, by simp⟩
  | insert a F _ ih =>
    obtain ⟨x, hx, hx0, hF⟩ := ih
    have hex : ∃ N : ℕ, (D a ^ N) x = 0 := hnil a x hx
    have hN := Nat.find_spec hex
    have hmin := fun m => Nat.find_min hex (m := m)
    set N := Nat.find hex with hNdef
    have hpos : N ≠ 0 := by
      intro h0
      rw [h0] at hN
      exact hx0 (by simpa using hN)
    obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    have hiter : ∀ k : ℕ, (D a ^ k) x ∈ I := by
      intro k
      induction k with
      | zero => simpa using hx
      | succ k ihk =>
        rw [pow_succ', Module.End.mul_apply]
        exact hstab a _ ihk
    refine ⟨(D a ^ M) x, hiter M, hmin M (by omega), ?_⟩
    intro Y hY
    rcases Finset.mem_insert.1 hY with rfl | hY
    · rw [← Module.End.mul_apply, ← pow_succ']
      rw [hM] at hN
      exact hN
    · have hc : Commute (D Y) (D a ^ M) := (hcomm Y a).pow_right M
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hF Y hY, map_zero]

theorem exists_joint_kernel_polynomial_family :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (I : Submodule ℂ V), I ≠ ⊥ →
      ∀ (D : ℂ → Module.End ℂ V), (∀ Y Y', Commute (D Y) (D Y')) →
      (∀ Y, ∀ x ∈ I, D Y x ∈ I) → (∀ Y, ∀ x ∈ I, ∃ N : ℕ, (D Y ^ N) x = 0) →
      ∀ (l : ℕ) (c : ℕ → Module.End ℂ V), (∀ Y, D Y = ∑ j ∈ Finset.range l, Y ^ j • c j) →
      ∃ w ∈ I, w ≠ 0 ∧ ∀ Y, D Y w = 0 := by
  intro V _ _ I hI D hcomm hstab hnil l c hD
  classical
  let F : Finset ℂ := (Finset.range l).image (fun n : ℕ => (n : ℂ))
  have hcard : F.card = l := by
    simpa using Finset.card_image_of_injective (Finset.range l)
      (Nat.cast_injective (R := ℂ))
  obtain ⟨w, hw, hw0, hF⟩ := exists_joint_kernel_finset I hI D hcomm hstab hnil F
  refine ⟨w, hw, hw0, fun Y => ?_⟩
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (D Y w)).1 fun φ => ?_
  let p : Polynomial ℂ :=
    ∑ j ∈ Finset.range l, Polynomial.C (φ (c j w)) * Polynomial.X ^ j
  have heval : ∀ Z : ℂ, p.eval Z = φ (D Z w) := by
    intro Z
    rw [hD Z]

    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hdeg : p.degree < (F.card : ℕ) := by
    rw [hcard]
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe l)).2 fun j hj => ?_
    refine (Polynomial.degree_C_mul_X_pow_le j _).trans_lt ?_
    exact WithBot.coe_lt_coe.2 (Finset.mem_range.1 hj)
  have hp : p = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero F hdeg
      (fun Z hZ => by rw [heval, hF Z hZ, map_zero])
  rw [← heval, hp, Polynomial.eval_zero]

end GlobalTheory.CompanionTheory.RgTransport
