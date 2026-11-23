module

public import Formalism.GaloisCohomology.Statement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.subqLen :
    ∀ (l : ℕ) [Fact l.Prime] (N : Submodule ℤ_[l] (QZ l)) (Q P : Type) [AddCommGroup Q] [Module ℤ_[l] Q] [AddCommGroup P] [Module ℤ_[l] P] (π : N →ₗ[ℤ_[l]] Q) (j : P →ₗ[ℤ_[l]] Q),
      Function.Surjective π → Function.Injective j → (∀ x : P, (l : ℤ_[l]) • x = 0) → Module.length ℤ_[l] P ≤ 1 := by
  intro l _ N Q P _ _ _ _ π j hπ hj htor
  have key : ∀ a b : QZ l, ∃ c : ℤ_[l], a = c • b ∨ b = c • a := by
    intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) b
    have step : ∀ x y : ℚ_[l], ‖x‖ ≤ ‖y‖ → ∃ c : ℤ_[l], x = c • y := by
      intro x y h
      by_cases hy : y = 0
      · subst hy
        refine ⟨0, ?_⟩
        rw [norm_zero] at h
        rw [norm_le_zero_iff.mp h, zero_smul]
      · refine ⟨⟨x / y, ?_⟩, ?_⟩
        · rw [PadicInt.mem_subring_iff, norm_div]
          exact div_le_one_of_le₀ h (norm_nonneg _)
        · show x = (x / y) * y
          rw [div_mul_cancel₀ _ hy]
    rcases le_total ‖x‖ ‖y‖ with h | h
    · obtain ⟨c, hc⟩ := step x y h
      exact ⟨c, Or.inl (by rw [hc]; rfl)⟩
    · obtain ⟨c, hc⟩ := step y x h
      exact ⟨c, Or.inr (by rw [hc]; rfl)⟩
  have hQ : ∀ q1 q2 : Q, ∃ c : ℤ_[l], q1 = c • q2 ∨ q2 = c • q1 := by
    intro q1 q2
    obtain ⟨n1, rfl⟩ := hπ q1
    obtain ⟨n2, rfl⟩ := hπ q2
    obtain ⟨c, h | h⟩ := key (n1 : QZ l) (n2 : QZ l)
    · refine ⟨c, Or.inl ?_⟩
      rw [← map_smul]
      congr 1
      exact Subtype.ext h
    · refine ⟨c, Or.inr ?_⟩
      rw [← map_smul]
      congr 1
      exact Subtype.ext h
  have hP : ∀ x y : P, x ≠ 0 → y ∈ Submodule.span ℤ_[l] {x} := by
    intro x y hx
    obtain ⟨c, h | h⟩ := hQ (j y) (j x)
    · rw [← map_smul] at h
      rw [hj h]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    · rw [← map_smul] at h
      have hxy := hj h
      by_cases hc : IsUnit c
      · obtain ⟨u, rfl⟩ := hc
        have hy : y = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • x := by
          rw [hxy, smul_smul, Units.inv_mul, one_smul]
        rw [hy]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
      · exfalso
        have hn : ‖c‖ < 1 := PadicInt.mem_nonunits.mp hc
        obtain ⟨d, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd c).mp hn
        apply hx
        rw [hxy, mul_comm, mul_smul, htor, smul_zero]
  rcases subsingleton_or_nontrivial P with hsub | hnt
  · rw [Module.length_eq_zero]
    exact zero_le
  · haveI : IsSimpleModule ℤ_[l] P := by
      rw [isSimpleModule_iff]
      refine IsSimpleOrder.mk (fun S => ?_)
      by_cases hS : S = ⊥
      · exact Or.inl hS
      · right
        obtain ⟨x, hxS, hx0⟩ := (Submodule.ne_bot_iff S).mp hS
        rw [eq_top_iff]
        intro y _
        exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxS)) (hP x y hx0)
    rw [Module.length_eq_one]
