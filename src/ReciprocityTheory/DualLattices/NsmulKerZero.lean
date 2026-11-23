module

public import ReciprocityTheory.DualLattices.NsetExpInjectiveSurjective
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

@[expose] public section

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace ATower

variable {p : ℕ} (Tw : ATower R₀ p)

lemma ξmul_surj (n : ℕ) : Function.Surjective (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) := by
  rintro ⟨k, hk⟩
  have hk' : k ∈ Ideal.span {Tw.ξ n} := by
    rw [← Tw.ker_eq n]
    simpa using hk
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hk'
  refine ⟨a, Subtype.ext ?_⟩
  show Tw.ξ n * a = k
  rw [← ha, mul_comm]

lemma exists_factor (n : ℕ) : ∃ g' : (Tw.π n).ker →ₗ[R₀] (Tw.R n : Type u),
    g' ∘ₗ ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) = (Tw.π n).1.toLinearMap := by
  have hle : LinearMap.ker (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) ≤
      LinearMap.ker (Tw.π n).1.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : Tw.ξ n * a = 0 := congrArg Subtype.val ha
    have hm : a ∈ Ideal.span {Tw.ξ n} := Tw.ann n a (by rw [mul_comm]; exact h0)
    rw [← Tw.ker_eq n, RingHom.mem_ker] at hm
    exact hm
  have hs := Tw.ξmul_surj n
  refine ⟨(LinearMap.ker _).liftQ _ hle ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _ hs).symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun a => ?_
  have h1 : (LinearMap.quotKerEquivOfSurjective _ hs).symm (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) a) =
      Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]

end ATower

namespace BX

variable (B : BX R₀) {p : ℕ}

lemma nsmul_ker_zero (Tw : ATower R₀ p) (n : ℕ) (V : B.gg ⊗[R₀] (Tw.π n).ker) :
    (p ^ (n + 1)) • V = 0 := by
  have hc : ((p : (Tw.R' n : Type u))) ^ (n + 1) = 0 := by exact_mod_cast Tw.char n
  induction V using TensorProduct.induction_on with
  | zero => simp
  | tmul g k =>
    have hk : (p ^ (n + 1)) • k = 0 := by
      apply Subtype.ext
      simp [nsmul_eq_mul, hc]
    rw [← TensorProduct.tmul_smul, hk, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

lemma exists_lift (Tw : ATower R₀ p) (n : ℕ) (y : B.G (Tw.R n)) (hy : (p ^ (n + 1)) • y = 0) :
    ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)), B.map (Tw.π n) th = y ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) := by
  obtain ⟨th, hth⟩ := B.surj (Tw.π n) (Tw.sqZero n) y
  have h0 : B.map (Tw.π n) ((p ^ (n + 1)) • th) = 0 := by rw [map_nsmul, hth, hy]
  obtain ⟨v, hv⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 h0
  obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective B.gg (Tw.ξmul_surj n) v
  exact ⟨th, w, hth, by rw [← hv, ← hw]; rfl⟩

lemma lift_indep (Tw : ATower R₀ p) (n : ℕ) (th th' : B.G (Tw.R' n)) (w w' : B.gg ⊗[R₀] (Tw.R' n : Type u))
    (he : B.map (Tw.π n) th = B.map (Tw.π n) th')
    (hw : (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w))
    (hw' : (p ^ (n + 1)) • th' = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w')) :
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w = LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w' := by
  have hd : B.map (Tw.π n) (th - th') = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨v0, hv0⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 hd
  have hp : (p ^ (n + 1)) • th = (p ^ (n + 1)) • th' := by
    have h : (p ^ (n + 1)) • (th - th') = 0 := by
      rw [← hv0, ← map_nsmul, B.nsmul_ker_zero Tw n v0, map_zero]
    rwa [smul_sub, sub_eq_zero] at h
  rw [hw, hw'] at hp
  have hx := B.tg_inj (Tw.π n) (Tw.sqZero n) hp
  obtain ⟨g', hg'⟩ := Tw.exists_factor n
  rw [← hg', LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (LinearMap.lTensor B.gg g') hx

end BX

end ReciprocityTheory.PGsh
