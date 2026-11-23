module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Gam

variable {A B : Type*} [CommRing A] [Field B] (i : A →+* B) (t : A)
  {H N Q : Type*} [AddCommGroup H] [Module A H] [AddCommGroup N] [Module A N] [AddCommGroup Q]
  (β : H →ₗ[A] N) (κ : H →+ (Q →+ B))

def F (n : ℕ) (x : N → H) (y : N) (φ : Q) : B := (i t ^ n)⁻¹ * κ (x y) φ

variable {i t β κ}

theorem key (hlin : ∀ (c : A) (x : H) (φ : Q), κ (c • x) φ = i c * κ x φ) (ht : i t ≠ 0)
    (hinj : ∃ n₀ : ℕ, ∀ x, β x = 0 → t ^ n₀ • x = 0) {n : ℕ} {x : N → H} (hx : ∀ y, β (x y) = t ^ n • y)
    {c : A} {x' : H} {y : N} (h : β x' = c • y) (φ : Q) : κ x' φ = i c * F i t κ n x y φ := by
  obtain ⟨n₀, h₀⟩ := hinj
  have h1 : β (t ^ n • x' - c • x y) = 0 := by
    rw [map_sub, map_smul, map_smul, h, hx, smul_smul, smul_smul, mul_comm, sub_self]
  have h2 : κ (t ^ n₀ • (t ^ n • x' - c • x y)) φ = 0 := simp [h₀ _ h1]
  simp only [smul_sub, map_sub, AddMonoidHom.sub_apply, hlin, map_pow] at h2
  have hn0 : i t ^ n₀ ≠ 0 := pow_ne_zero _ ht
  have hn : i t ^ n ≠ 0 := pow_ne_zero _ ht
  have h3 : i t ^ n * κ x' φ = i c * κ (x y) φ := by
    apply mul_left_cancel₀ hn0; linear_combination h2
  unfold F
  field_simp
  linear_combination h3

def hom (hlin : ∀ (c : A) (x : H) (φ : Q), κ (c • x) φ = i c * κ x φ) (ht : i t ≠ 0)
    (hinj : ∃ n₀ : ℕ, ∀ x, β x = 0 → t ^ n₀ • x = 0) (n : ℕ) (x : N → H) (hx : ∀ y, β (x y) = t ^ n • y) :
    N →+ (Q →+ B) :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun φ => F i t κ n x y φ) (by intro a b; simp [F, mul_add]))
    (by
      intro y y'
      ext φ
      have e := key hlin ht hinj hx (x' := x y + x y') (c := t ^ n) (y := y + y') (by simp [hx, smul_add]) φ
      have hn : i t ^ n ≠ 0 := pow_ne_zero _ ht
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [map_add (f := _), AddMonoidHom.add_apply, map_pow] at e
      unfold F at e ⊢
      field_simp
      field_simp at e
      linear_combination -e)

theorem hom_key (hlin : ∀ (c : A) (x : H) (φ : Q), κ (c • x) φ = i c * κ x φ) (ht : i t ≠ 0)
    (hinj : ∃ n₀ : ℕ, ∀ x, β x = 0 → t ^ n₀ • x = 0) (n : ℕ) (x : N → H) (hx : ∀ y, β (x y) = t ^ n • y)
    {c : A} {x' : H} {y : N} (h : β x' = c • y) (φ : Q) : κ x' φ = i c * hom hlin ht hinj n x hx y φ :=
  key hlin ht hinj hx h φ

end CrystallineSemistableComparison.Gam
