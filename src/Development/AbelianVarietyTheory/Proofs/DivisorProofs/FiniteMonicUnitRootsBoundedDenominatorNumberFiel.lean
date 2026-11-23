module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem monic_roots_norm_one_coeff_denom_finite : ∀ (E : Type) [Field E] [NumberField E] (n d : ℕ), d ≠ 0 → {P : E[X] | P.Monic ∧ P.natDegree = n ∧ (∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) ∧ ∀ k, ∃ a : 𝓞 E, (a : E) = d * P.coeff k}.Finite := by
  intro E _ _ n d hd
  set T := {P : E[X] | P.Monic ∧ P.natDegree = n ∧ (∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) ∧ ∀ k, ∃ a : 𝓞 E, (a : E) = d * P.coeff k} with hT
  set B : ℝ := max 1 1 ^ n * (n.choose (n / 2) : ℝ) with hB
  set S : Set E := {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ) * B} with hS
  have hSf : S.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ ((d : ℝ) * B)
  let F : E[X] → (Fin (n+1) → E) := fun P k => (d : E) * P.coeff k
  have hpi : (Set.pi Set.univ (fun _ : Fin (n+1) => S)).Finite := Set.Finite.pi (fun _ => hSf)
  have himg : F '' T ⊆ Set.pi Set.univ (fun _ : Fin (n+1) => S) := by
    rintro _ ⟨P, ⟨hm, hn, hr, hc⟩, rfl⟩ k _
    obtain ⟨a, ha⟩ := hc k
    refine ⟨?_, fun φ => ?_⟩
    · show IsIntegral ℤ ((d : E) * P.coeff k)
      rw [← ha]; exact a.isIntegral_coe
    · have hbd := Polynomial.coeff_bdd_of_roots_le (B := 1) (d := n) φ hm (IsAlgClosed.splits _) hn.le
        (fun z hz => (hr φ z hz).le) k
      rw [Polynomial.coeff_map] at hbd
      show ‖φ ((d : E) * P.coeff k)‖ ≤ (d : ℝ) * B
      rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left hbd (Nat.cast_nonneg d)
  have hinj : Set.InjOn F T := by
    rintro P ⟨-, hP, -⟩ Q ⟨-, hQ, -⟩ hPQ
    ext k
    by_cases hk : k < n + 1
    · have := congrFun hPQ ⟨k, hk⟩
      simp only [F] at this
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hd) this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  exact Set.Finite.of_finite_image (hpi.subset himg) hinj

end GlobalTheory
