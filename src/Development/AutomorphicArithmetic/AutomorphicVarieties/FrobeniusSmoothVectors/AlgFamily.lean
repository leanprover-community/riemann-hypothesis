module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgQuot
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_family :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D) (ρ : NRep F n D), IsVertexRing C 𝔪 → IsModel O C 𝔪 ρ → ∃ f : ∀ N : ℕ, S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1), (∀ N, S.ρ.map (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) = ρ.map (Ideal.Quotient.mk (𝔪 ^ (N + 1)))) ∧ (∀ N x d, Ideal.Quotient.mk (𝔪 ^ (N + 1 + 1)) d = f (N + 1) x → Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = f N x) ∧ ∀ N, ∀ x ∈ maximalIdeal S.R ^ (N + 1), f N x = 0 := by
  intro l _ O _ _ F n S C _ _ _ D _ _ _ _ 𝔪 ρ hV hM
  choose hco hmax using alg_quot O C 𝔪 hV
  have hex : ∀ N, ∃! f : S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1),
      S.ρ.map (f : S.R →+* D ⧸ 𝔪 ^ (N + 1)) = ρ.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) := by
    intro N
    letI := hco N
    exact S.univ _ _ (alg_lift C 𝔪 ρ hM _ (Ideal.Quotient.mkₐ O (𝔪 ^ (N + 1))) (fun x hx => by
      rw [hmax N]
      exact Ideal.mem_map_of_mem _ hx))
  choose f hf huniq using hex
  refine ⟨f, hf, ?_, ?_⟩
  · intro N x d hd
    have hle : 𝔪 ^ (N + 1 + 1) ≤ 𝔪 ^ (N + 1) := Ideal.pow_le_pow_right (Nat.le_succ _)
    have hcomp : (Ideal.Quotient.factorₐ O hle).comp (f (N + 1)) = f N := by
      apply huniq N
      have e : (((Ideal.Quotient.factorₐ O hle).comp (f (N + 1)) : S.R →ₐ[O] D ⧸ 𝔪 ^ (N + 1)) :
          S.R →+* D ⧸ 𝔪 ^ (N + 1)) =
          ((Ideal.Quotient.factorₐ O hle : D ⧸ 𝔪 ^ (N + 1 + 1) →ₐ[O] D ⧸ 𝔪 ^ (N + 1)) :
            D ⧸ 𝔪 ^ (N + 1 + 1) →+* D ⧸ 𝔪 ^ (N + 1)).comp (f (N + 1) : S.R →+* D ⧸ 𝔪 ^ (N + 1 + 1)) := rfl
      rw [e, ← NRep.map_map, hf (N + 1), NRep.map_map]
      rfl
    rw [← hcomp, AlgHom.comp_apply, ← hd]
    rfl
  · intro N x hx
    letI := hco N
    have hm : ∀ y ∈ maximalIdeal S.R,
        f N y ∈ Ideal.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) 𝔪 := by
      intro y hy
      rw [← hmax N, ← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hy
    have hle : Ideal.map (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) (maximalIdeal S.R) ≤
        Ideal.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) 𝔪 := by
      rw [Ideal.map_le_iff_le_comap]
      exact hm
    have hx' := Ideal.mem_map_of_mem (f N : S.R →+* D ⧸ 𝔪 ^ (N + 1)) hx
    rw [Ideal.map_pow] at hx'
    have h2 := Ideal.pow_right_mono hle (N + 1) hx'
    rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot] at h2
    exact h2
