module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NonsqMul
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.signLaw : UpperTheory.V.Z.Sym.Loc.SignLaw := by
  intro O K _ _ _ _ _ Δ τ L hD lam y hl hX hX'
  haveI := L.frac
  have h0 : Δ ≠ 0 := by
    obtain ⟨u, s, hs, e⟩ := L.even
    rw [e]
    exact mul_ne_zero (u.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs)
  have hN : QuadraticAlgebra.norm (y : Lsq K Δ) ≠ 0 := (QuadraticAlgebra.isUnit_iff_norm_isUnit.1 y.isUnit).ne_zero
  set l' := lam * star (y : Lsq K Δ) * ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) with hl'
  have e1 : QuadraticAlgebra.norm (y : Lsq K Δ) • l' = lam * star (y : Lsq K Δ) ^ 2 := by
    rw [Algebra.smul_def, QuadraticAlgebra.algebraMap_norm_eq_mul_star, hl']
    linear_combination (lam * star (y : Lsq K Δ) ^ 2) * y.mul_inv
  have e2 := congrArg QuadraticAlgebra.trace e1
  rw [map_smul, smul_eq_mul] at e2
  unfold eps
  set N := QuadraticAlgebra.norm (y : Lsq K Δ) with hNd
  set X := 2 + τ + QuadraticAlgebra.trace lam with hXd
  set X' := 2 + τ + QuadraticAlgebra.trace l' with hXd'
  have key : (2 * (lam.re * (y : Lsq K Δ).re - Δ * lam.im * (y : Lsq K Δ).im) + (y : Lsq K Δ).re * (2 + τ)) ^ 2 -
      ((τ ^ 2 - 4) * Δ) * (y : Lsq K Δ).im ^ 2 = X * X' * N := by
    have e3 : X' * N = (2 + τ) * N + QuadraticAlgebra.trace (lam * star (y : Lsq K Δ) ^ 2) := by rw [← e2, hXd']; ring
    rw [mul_assoc X, e3, hXd, hNd]
    rw [QuadraticAlgebra.norm_def] at hl
    simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.trace_def, sq] at hl ⊢
    linear_combination (-4 * Δ * (y : Lsq K Δ).im ^ 2) * hl
  have hP : X * X' * N ≠ 0 := mul_ne_zero (mul_ne_zero hX hX') hN
  have H := hsLaw O K Δ L
  have h1 : hs (τ ^ 2 - 4) (X * X' * N) * hs Δ (X * X' * N) = 1 := by
    rw [H.1 _ _ hD hP, H.1 _ _ h0 hP, ← hsMul O K Δ L _ _ _ hP hD h0, H.1 _ _ hP (mul_ne_zero hD h0)]
    exact if_pos ⟨_, _, key⟩
  have h2 : hs Δ N = 1 := if_pos ⟨(y : Lsq K Δ).re, (y : Lsq K Δ).im, by rw [hNd, QuadraticAlgebra.norm_def]; ring⟩
  rw [hsMul O K Δ L _ _ _ hD (mul_ne_zero hX hX') hN, hsMul O K Δ L _ _ _ hD hX hX', hsMul O K Δ L _ _ _ h0 (mul_ne_zero hX hX') hN,
    hsMul O K Δ L _ _ _ h0 hX hX', h2] at h1
  have hq : ∀ D x : K, hs D x * hs D x = 1 := fun D x => by unfold hs; split_ifs <;> norm_num
  have a := hq (τ ^ 2 - 4) X'
  have b := hq Δ X'
  linear_combination (-hs (τ ^ 2 - 4) X' * hs Δ X') * h1 +
    (hs (τ ^ 2 - 4) X * hs (τ ^ 2 - 4) N * hs Δ X * hs Δ X' * hs Δ X') * a + (hs (τ ^ 2 - 4) X * hs (τ ^ 2 - 4) N * hs Δ X) * b
