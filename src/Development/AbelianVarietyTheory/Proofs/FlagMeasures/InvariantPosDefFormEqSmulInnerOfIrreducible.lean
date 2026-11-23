module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem exists_endomorphism_representing_sesquilinear_form
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : ∃ A : W →ₗ[ℂ] W, ∀ x y, B x y = ⟪x, A y⟫_ℂ := by
  classical
  let e := stdOrthonormalBasis ℂ W
  refine ⟨∑ j, (B (e j)).smulRight (e j), fun x y => ?_⟩
  conv_lhs => rw [← e.sum_repr' x]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
  LinearMap.smulRight_apply, inner_sum, inner_smul_right, smul_eq_mul, inner_conj_symm]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem invariant_posDef_form_eq_smul_inner_of_irreducible :
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (I : Type) (π : I → (W →L[ℂ] W)) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ i v, ‖π i v‖ = ‖v‖) → (∀ S : Submodule ℂ W, (∀ i, ∀ v ∈ S, π i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i x y, B (π i x) (π i y) = B x y) → (∀ x y, B y x = star (B x y)) → (∀ x, x ≠ 0 → 0 < (B x x).re) → ∃ c : ℝ, 0 < c ∧ (Nontrivial W → ∀ x y, B x y = c * ⟪x, y⟫_ℂ) := by
  intro W _ _ _ I π B hiso hirr hinv hherm hpos
  rcases subsingleton_or_nontrivial W with hW | hW
  · exact ⟨1, one_pos, fun h => absurd h (not_nontrivial W)⟩
  obtain ⟨A, hA⟩ := exists_endomorphism_representing_sesquilinear_form W B
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hAv : A v = μ • v := hv.apply_eq_smul
  have hinner : ∀ i x y, ⟪π i x, π i y⟫_ℂ = ⟪x, y⟫_ℂ := fun i x y =>
    (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).inner_map_map x y
  have hsurj : ∀ i, Function.Surjective (π i) := fun i =>
    (LinearMap.injective_iff_surjective (f := (π i : W →ₗ[ℂ] W))).1
      (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).injective
  let S : Submodule ℂ W :=
    { carrier := {y | ∀ x, B x y = μ * ⟪x, y⟫_ℂ}
      add_mem' := fun {a b} ha hb x => by
        rw [map_add (f := _), inner_add_right, ha x, hb x, mul_add]
      zero_mem' := fun x => by simp
      smul_mem' := fun c a ha x => by
        rw [map_smul, inner_smul_right, ha x, smul_eq_mul]; ring }
  have hS : ∀ y, y ∈ S ↔ ∀ x, B x y = μ * ⟪x, y⟫_ℂ := fun y => Iff.rfl
  have hvS : v ∈ S := by
    rw [hS]; intro x
    rw [hA, hAv, inner_smul_right]
  have hstab : ∀ i, ∀ y ∈ S, π i y ∈ S := by
    intro i y hy
    rw [hS] at hy ⊢
    intro x
    obtain ⟨x', rfl⟩ := hsurj i x
    rw [hinv, hinner, hy]
  have htop : S = ⊤ := by
    rcases hirr S hstab with h | h
    · rw [h] at hvS
      exact absurd ((Submodule.mem_bot ℂ).1 hvS) hv0
    · exact h
  have hall : ∀ x y, B x y = μ * ⟪x, y⟫_ℂ := fun x y =>
    (hS y).1 (htop ▸ Submodule.mem_top) x
  have hvv : B v v = μ * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hall, inner_self_eq_norm_sq_to_K]; simp
  have hn : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv0) 2
  have him : μ.im = 0 := by
    have h1 := congrArg Complex.im (hherm v v)
    rw [hvv] at h1
    simp only [Complex.star_def, Complex.conj_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, mul_zero, zero_add] at h1
    have h2 : μ.im * ‖v‖ ^ 2 = 0 := by linarith
    exact (mul_eq_zero.1 h2).resolve_right hn.ne'
  have hre : 0 < μ.re := by
    have h1 := hpos v hv0
    rw [hvv] at h1
    simp only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero] at h1
    exact (mul_pos_iff_of_pos_right hn).1 h1
  refine ⟨μ.re, hre, fun _ x y => ?_⟩
  have : (μ.re : ℂ) = μ := Complex.ext rfl (by simp [him])
  rw [this, hall]

end GlobalTheory
