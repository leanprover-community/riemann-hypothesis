module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.descent :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ → ∀ (s : K) (ε : Oˣ), Δ * s ^ 2 = algebraMap O K ε →
    ∀ x : Lsq K Δ, (IsInt O x ↔ x.re ∈ (algebraMap O K).range ∧ ∃ b : O, x.im = s * algebraMap O K b) ∧ (IsInt O x → IsInt O (star x)) := by
  intro O K _ _ _ _ _ Δ hL s ε hs x
  haveI := hL.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hstar : ∀ y : Lsq K Δ, IsIntegral O y → IsIntegral O (star y) := by
    intro y hy
    let f : Lsq K Δ →ₐ[O] Lsq K Δ :=
      { starRingEnd (Lsq K Δ) with
        commutes' := fun r => by
          show star (algebraMap O (Lsq K Δ) r) = algebraMap O (Lsq K Δ) r
          rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
          ext <;> simp }
    exact hy.map f
  have hdown : ∀ c : K, IsIntegral O (algebraMap K (Lsq K Δ) c) → c ∈ (algebraMap O K).range := by
    intro c hc
    have hc' : IsIntegral O c :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (Lsq K Δ))
        (algebraMap K (Lsq K Δ)).injective).mp hc
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hc'
    exact ⟨y, hy⟩
  have hεne : algebraMap O K (ε : O) ≠ 0 := (map_ne_zero_iff _ hinj).mpr ε.ne_zero
  have hΔs : Δ * s ^ 2 ≠ 0 := by rw [hs]; exact hεne
  have hΔ : Δ ≠ 0 := left_ne_zero_of_mul hΔs
  have hs0 : s ≠ 0 := fun h => hΔs (by simp [h])
  have hfwd : IsIntegral O x →
      x.re ∈ (algebraMap O K).range ∧ ∃ b : O, x.im = s * algebraMap O K b := by
    intro hxi
    have hsx := hstar x hxi
    have htr : x + star x = algebraMap K (Lsq K Δ) (2 * x.re) := by
      ext <;> simp <;> ring
    have hnm : x * star x = algebraMap K (Lsq K Δ) (x.re * x.re - Δ * x.im * x.im) := by
      ext <;> simp <;> ring
    obtain ⟨t, ht⟩ := hdown _ (htr ▸ hxi.add hsx)
    obtain ⟨n, hn⟩ := hdown _ (hnm ▸ hxi.mul hsx)
    obtain ⟨u, hu⟩ := hL.two.exists_left_inv
    have hu2 : algebraMap O K u * 2 = 1 := by
      have := congrArg (algebraMap O K) hu
      rwa [map_mul, map_ofNat, map_one] at this
    have hre : algebraMap O K (u * t) = x.re := by
      rw [map_mul, ht, ← mul_assoc, hu2, one_mul]
    refine ⟨⟨u * t, hre⟩, ?_⟩
    have hεK : algebraMap O K ((ε⁻¹ : Oˣ) : O) * algebraMap O K (ε : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have he' : algebraMap O K ((ε⁻¹ : Oˣ) : O) = (Δ * s ^ 2)⁻¹ := by
      rw [hs]; exact eq_inv_of_mul_eq_one_left hεK
    have hb2 : (x.im / s) ^ 2 =
        algebraMap O K (((ε⁻¹ : Oˣ) : O) * ((u * t) * (u * t) - n)) := by
      rw [map_mul, map_sub, map_mul, he', hre, hn]
      field_simp
      ring
    have hbi : IsIntegral O (x.im / s) := by
      refine IsIntegral.of_pow two_pos ?_
      rw [hb2]
      exact isIntegral_algebraMap
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hbi
    refine ⟨b, ?_⟩
    rw [hb]
    field_simp
  have hbwd : (x.re ∈ (algebraMap O K).range ∧ ∃ b : O, x.im = s * algebraMap O K b) →
      IsIntegral O x := by
    rintro ⟨⟨a, ha⟩, b, hb⟩
    have hω : IsIntegral O (algebraMap K (Lsq K Δ) s * ω) := by
      refine IsIntegral.of_pow two_pos ?_
      have hsq : (algebraMap K (Lsq K Δ) s * ω) ^ 2 = algebraMap O (Lsq K Δ) ε := by
        rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ), ← hs, sq]
        ext
        · simp only [re_mul, im_mul, algebraMap_re, algebraMap_im, omega_re, omega_im]
          ring
        · simp only [re_mul, im_mul, algebraMap_re, algebraMap_im, omega_re, omega_im]
          ring
      rw [hsq]
      exact isIntegral_algebraMap
    have hxe : x = algebraMap O (Lsq K Δ) a +
        algebraMap O (Lsq K Δ) b * (algebraMap K (Lsq K Δ) s * ω) := by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ) a,
        IsScalarTower.algebraMap_apply O K (Lsq K Δ) b, ha]
      ext <;> simp [hb] <;> ring
    rw [hxe]
    exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul hω)
  exact ⟨⟨hfwd, hbwd⟩, hstar x⟩
