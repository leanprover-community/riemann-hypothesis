module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

theorem UpperTheory.Reformulated.B.SimultaneousEigenvectorInvariantSubspace.simEig :
    ∀ {K M : Type} [inst : Field K] [IsAlgClosed K] [inst_2 : AddCommGroup M]
    [inst_3 : _root_.Module K M] [FiniteDimensional K M] {J : Type} (T : J → Module.End K M),
    (∀ (i j : J), T i * T j = T j * T i) →
      ∀ (d : ℕ) (U : Submodule K M),
        Module.finrank K ↥U = d →
          U ≠ ⊥ →
            (∀ (j : J), ∀ x ∈ U, (T j : M → M) x ∈ U) →
              ∃ v ∈ U, v ≠ (0 : M) ∧ ∀ (j : J), ∃ (c : K), (T j : M → M) v = c • v := by
  intro K M _ _ _ _ _ J T hT d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hd hU hinv
    by_cases h : ∀ j, ∃ c : K, ∀ x ∈ U, T j x = c • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      refine ⟨v, hv, hv0, fun j => ?_⟩
      obtain ⟨c, hc⟩ := h j
      exact ⟨c, hc v hv⟩
    · rw [not_forall] at h
      obtain ⟨i, hi⟩ := h
      haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((T i).restrict (hinv i) : Module.End K U)
      obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
      have hw1 : T i (w : M) = c • (w : M) := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [LinearMap.restrict_apply] using h1
      have hw0 : (w : M) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
      have hlt : U ⊓ (T i).eigenspace c < U := by
        refine lt_of_le_of_ne inf_le_left fun heq => hi ⟨c, fun x hx => ?_⟩
        rw [← heq] at hx
        exact Module.End.mem_eigenspace_iff.mp hx.2
      have hne : U ⊓ (T i).eigenspace c ≠ ⊥ := by
        intro h0
        have hm : (w : M) ∈ U ⊓ (T i).eigenspace c :=
          ⟨w.2, Module.End.mem_eigenspace_iff.mpr hw1⟩
        rw [h0] at hm
        exact hw0 ((Submodule.mem_bot K).mp hm)
      have hst : ∀ j, ∀ x ∈ U ⊓ (T i).eigenspace c, T j x ∈ U ⊓ (T i).eigenspace c := by
        intro j x hx
        refine ⟨hinv j x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h2 : T i x = c • x := Module.End.mem_eigenspace_iff.mp hx.2
        have h3 := LinearMap.congr_fun (hT i j) x
        simp only [Module.End.mul_apply] at h3
        rw [h3, h2, map_smul]
      obtain ⟨v, hv, hv0, hvj⟩ :=
        ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne hst
      exact ⟨v, hv.1, hv0, hvj⟩
