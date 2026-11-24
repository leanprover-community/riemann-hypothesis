module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem dualform : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) →
    ∀ lam : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ, ∃ u : κ → mixedEmbedding.mixedSpace F,
      ∀ x, ℓ (∑ k, x k * u k) = lam x := by
  intro F _ _ κ _ ℓ hℓ lam
  set M := mixedEmbedding.mixedSpace F
  let Φ : (κ → M) →ₗ[ℝ] Module.Dual ℝ (κ → M) :=
    { toFun := fun u =>
        { toFun := fun x => ℓ (∑ k, x k * u k)
          map_add' := by intro x y; simp [add_mul, Finset.sum_add_distrib]
          map_smul' := by intro c x; simp [smul_mul_assoc, ← Finset.smul_sum] }
      map_add' := by
        intro u v; refine LinearMap.ext fun x => ?_
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c u; refine LinearMap.ext fun x => ?_
        simp [mul_smul_comm, ← Finset.smul_sum] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext k
    by_contra hne
    obtain ⟨w, hw⟩ := hℓ (u k) hne
    apply hw
    have := LinearMap.congr_fun hu (Pi.single k w)
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at this
    rw [Finset.sum_eq_single k] at this
    · simpa [mul_comm] using this
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hsurj : Function.Surjective Φ := by
    have : Module.finrank ℝ (κ → M) = Module.finrank ℝ (Module.Dual ℝ (κ → M)) :=
      (Subspace.dual_finrank_eq).symm
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).mp hinj
  obtain ⟨u, hu⟩ := hsurj lam
  exact ⟨u, fun x => by rw [← hu]; rfl⟩

end GlobalTheory
