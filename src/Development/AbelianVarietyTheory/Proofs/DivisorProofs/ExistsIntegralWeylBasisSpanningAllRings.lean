module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLKBasis
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

open Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.WeylBasis

theorem map_mem_span {σ ι : Type} (R : Type) [CommRing R] (g : ι → MvPolynomial σ ℤ) {f : MvPolynomial σ ℤ}
    (hf : f ∈ Submodule.span ℤ (Set.range g)) :
    MvPolynomial.map (Int.castRingHom R) f ∈
      Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (g i)) := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy => rw [map_zsmul]; exact zsmul_mem hy a

theorem weyl_finite (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) : Module.Finite ℤ (weyl ℤ n n le_rfl ν) := by
  obtain ⟨c, hc, -⟩ := sSBasis ℤ n n ν
  have : Finite (ssIdx n n ν) := (sSIdxFinite n n ν).to_subtype
  have : Module.Finite ℤ (dualWeyl ℤ n n ν) := by
    rw [← hc.2.1]
    exact Module.Finite.span_of_finite ℤ (Set.finite_range c)
  exact Module.Finite.of_injective (Submodule.inclusion (weylLeDual ℤ n n le_rfl ν hν))
    (Submodule.inclusion_injective _)

theorem exists_weyl_basis : ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∃ (P : Type) (_ : Fintype P) (b : P → MvPolynomial (Fin n × Fin n) ℤ), LinearIndependent ℤ b ∧ (∀ (R : Type) [CommRing R], weyl R n n le_rfl ν = Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (b i))) ∧ ∀ (K : Type) [Field K] [CharZero K], dualWeyl K n n ν = Submodule.span K (Set.range fun i => MvPolynomial.map (Int.castRingHom K) (b i)) := by
  intro n ν hν
  have := weyl_finite n ν hν
  have : Module.Free ℤ (weyl ℤ n n le_rfl ν) := inferInstance
  let B := Module.Free.chooseBasis ℤ (weyl ℤ n n le_rfl ν)
  have hspan : Submodule.span ℤ (Set.range fun i => (B i : MvPolynomial (Fin n × Fin n) ℤ)) = weyl ℤ n n le_rfl ν := by
    have h := congrArg (Submodule.map (weyl ℤ n n le_rfl ν).subtype) B.span_eq
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at h
    exact h
  have hR : ∀ (R : Type) [CommRing R], weyl R n n le_rfl ν =
      Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (B i : MvPolynomial (Fin n × Fin n) ℤ)) := by
    intro R _
    apply le_antisymm
    · unfold weyl
      rw [Submodule.span_le]
      rintro _ ⟨w, rfl⟩
      have hw' : applyWord ℤ w (hw ℤ le_rfl ν) ∈ weyl ℤ n n le_rfl ν := Submodule.subset_span ⟨w, rfl⟩
      rw [← hspan] at hw'
      have h := map_mem_span R _ hw'
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map] at h
      exact h
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h := map_mem_span R (fun w : List (Fin n × Fin n × ℕ) => applyWord ℤ w (hw ℤ le_rfl ν)) (B i).2
      simp only [← lclosedeq_applyWord_map, lclosedeq_hw_map] at h
      exact h
  refine ⟨_, inferInstance, fun i => (B i : MvPolynomial (Fin n × Fin n) ℤ), ?_, hR, ?_⟩
  · exact B.linearIndependent.map' (weyl ℤ n n le_rfl ν).subtype (Submodule.ker_subtype _)
  · intro K _ _
    apply le_antisymm
    · obtain ⟨c, hc, -⟩ := sSBasis ℤ n n ν
      rw [← span_map_weightBasis_eq_dualWeyl (K := K) hc, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hj : c j ∈ dualWeyl ℤ n n ν := hc.2.1 ▸ Submodule.subset_span ⟨j, rfl⟩
      obtain ⟨m, hm, hmj⟩ := weylRational n n le_rfl ν hν _ hj
      rw [← hspan] at hmj
      have h := map_mem_span K _ hmj
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul K] at h
      exact (Submodule.smul_mem_iff _ (Int.cast_ne_zero.2 hm)).1 h
    · rw [← hR K]
      exact weylLeDual K n n le_rfl ν hν

end GlobalTheory.WeylBasis
