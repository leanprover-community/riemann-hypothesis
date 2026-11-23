module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.GramCore
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.OfMap

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

private theorem UpperTheory.V.Ws.Pp.gf_adj_mul {R : Type} [CommRing R] (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev] <;> ring

private theorem UpperTheory.V.Ws.Pp.gf_adj_one {R : Type} [CommRing R] : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]

private theorem UpperTheory.V.Ws.Pp.gf_conj {R : Type} [CommRing R] {ν : R} {X : M4 R} (h : IsGSp ν X) (u v : M4 R)
    (hv : v * u = 1) : adj (u * X * v) * (adj v * v) * (u * X * v) = ν • (adj v * v) := by
  have h1 : adj u * adj v = 1 := by
    rw [← gf_adj_mul, hv, gf_adj_one]
  unfold IsGSp at h
  rw [gf_adj_mul, gf_adj_mul]
  calc _ = adj v * (adj X * (adj u * adj v) * (v * u) * X) * v := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, hv, Matrix.mul_one, Matrix.mul_one, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

private theorem UpperTheory.V.Ws.Pp.gf_gram {K : Type} [Field K] {ν : K} {M A : M4 K} (hM : ∀ i j, j < i → M i j = 0)
    (h : adj M * A * M = ν • A)
    (hc : ∀ i j : Fin 4, j < i → M i.rev i.rev * M j j ≠ ν) : ∀ i j, j < i → A i j = 0 := by
  have e := fun i j => congrFun (congrFun h i) j
  have m10 := hM 1 0 (by decide)
  have m20 := hM 2 0 (by decide)
  have m30 := hM 3 0 (by decide)
  have m21 := hM 2 1 (by decide)
  have m31 := hM 3 1 (by decide)
  have m32 := hM 3 2 (by decide)
  have k : ∀ {a b x : K}, a ≠ b → a * x = b * x → x = 0 := fun hab hx => by
    by_contra h0
    exact hab (mul_right_cancel₀ h0 hx)
  have e30 := e 3 0
  have e20 := e 2 0
  have e10 := e 1 0
  have e31 := e 3 1
  have e21 := e 2 1
  have e32 := e 3 2
  simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, m10, m20, m30, m21, m31, m32] at e30 e20 e10 e31 e21 e32
  have a30 : A 3 0 = 0 := k (hc 3 0 (by decide)) (by show M 0 0 * M 0 0 * _ = _; linear_combination e30)
  rw [a30] at e20 e10 e31 e21 e32
  have a20 : A 2 0 = 0 := k (hc 2 0 (by decide)) (by show M 1 1 * M 0 0 * _ = _; linear_combination e20)
  have a31 : A 3 1 = 0 := k (hc 3 1 (by decide)) (by show M 0 0 * M 1 1 * _ = _; linear_combination e31)
  simp only [a20, a31] at e10 e21 e32
  have a10 : A 1 0 = 0 := k (hc 1 0 (by decide)) (by show M 2 2 * M 0 0 * _ = _; linear_combination e10)
  have a21 : A 2 1 = 0 := k (hc 2 1 (by decide)) (by show M 1 1 * M 1 1 * _ = _; linear_combination e21)
  have a32 : A 3 2 = 0 := k (hc 3 2 (by decide)) (by show M 0 0 * M 2 2 * _ = _; linear_combination e32)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption

theorem UpperTheory.V.Ws.Pp.genFlag :
    ∀ {H K : Type} [Group H] [Field K] (I : Subgroup H) (ps : Fin 4 → H → K) (s₀ : H) (ν : K) (r : H →* M4 K), s₀ ∈ I → Function.Injective (fun i => ps i s₀) → (∀ i, ps i s₀ * ps i.rev s₀ = ν) → ν ≠ 0 → IsGSp ν (r s₀) → Ord I ps s₀ r → ∃ h : M4 K, IsGSp 1 h ∧ (∀ g, IsUp (adj h * r g * h)) ∧ (∀ s ∈ I, ∀ i, (adj h * r s * h) i i = ps i s) ∧ ∀ i g, (∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀)) * (adj h * r g * h) i i = (prj (fun a => ps a s₀) (r s₀) i * r g).trace := by
  intro H K _ _ I ps s₀ ν r hs hinj hrev hν hg ho
  obtain ⟨u, κ, h1, h2, h3, h4⟩ := ordFlag I K ps s₀ r hinj ho
  have hA := gf_gram (h1 s₀) (gf_conj hg _ _ u.inv_mul) fun i j hij e => by
    rw [h2, h2, h3 _ _ hs, h3 _ _ hs, ← hrev i, mul_comm (ps i s₀)] at e
    have h0 : ps i.rev s₀ ≠ 0 := fun h => hν (by rw [← hrev i, h, mul_zero])
    exact hij.ne (hinj (mul_left_cancel₀ h0 e))
  obtain ⟨t, ht, hh⟩ := gram u⁻¹ hA
  have hadj : adj (((u⁻¹ : (M4 K)ˣ) : M4 K) * (t : M4 K)) = ((t⁻¹ : (M4 K)ˣ) : M4 K) * (u : M4 K) := by
    have e := adj_mul_self hh
    rw [← mul_assoc, Units.mul_eq_one_iff_eq_inv, Units.mul_inv_eq_iff_eq_mul] at e
    exact e
  have key : ∀ g, adj (((u⁻¹ : (M4 K)ˣ) : M4 K) * (t : M4 K)) * r g * (((u⁻¹ : (M4 K)ˣ) : M4 K) * (t : M4 K))
      = ((t⁻¹ : (M4 K)ˣ) : M4 K) * ((u : M4 K) * r g * ((u⁻¹ : (M4 K)ˣ) : M4 K)) * (t : M4 K) := fun g => by
    rw [hadj]
    simp only [mul_assoc]
  have up := fun g => upConj t.inv_mul (IsUp_inv ht) ht (h1 g)
  refine ⟨_, hh, fun g => ?_, fun s hs i => ?_, fun i g => ?_⟩
  · rw [key]
    exact (up g).1
  · rw [key, (up s).2, h2, h3 i s hs]
  · rw [key, (up g).2, h2, h4]
