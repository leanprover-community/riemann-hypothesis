module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

private theorem int_of_norm_one {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] {Δ τ : K} (h : IsLoc O Δ) (hτ : ¬ IsSquare (τ ^ 2 - 4)) (e : Etau K τ)
    (hn : QuadraticAlgebra.norm e = 1) : IsIntegral O e := by
  classical
  haveI := h.frac
  have hN : e.re * e.re + τ * e.re * e.im - (-1) * e.im * e.im = 1 := by
    have h' := hn
    rw [QuadraticAlgebra.norm_def] at h'
    exact h'
  by_cases hq : e.im = 0
  · have hp : (e.re - 1) * (e.re + 1) = 0 := by
      rw [hq] at hN
      linear_combination hN
    rcases mul_eq_zero.mp hp with h1 | h1
    · have he : e = 1 := by
        ext
        · simp
          linear_combination h1
        · simp [hq]
      rw [he]
      exact isIntegral_one
    · have he : e = -1 := by
        ext
        · simp
          linear_combination h1
        · simp [hq]
      rw [he]
      exact isIntegral_one.neg
  · have h2K : (2 : K) ≠ 0 := by
      have h2 := h.two.map (algebraMap O K)
      rw [map_ofNat] at h2
      exact h2.ne_zero
    have nz : ∀ x y : K, y ≠ 0 → x * x + τ * x * y + y * y ≠ 0 := by
      intro x y hy hxy
      apply hτ
      refine ⟨2 * x / y + τ, ?_⟩
      field_simp
      linear_combination (-4) * hxy
    obtain ⟨t, ht⟩ : ∃ t : O, algebraMap O K t = QuadraticAlgebra.trace e := by
      by_contra hne
      push_neg at hne
      have hTd : QuadraticAlgebra.trace e = 2 * e.re + τ * e.im := QuadraticAlgebra.trace_def e
      set T := QuadraticAlgebra.trace e with hTdef
      have hT0 : T ≠ 0 := fun h0 => hne 0 (by rw [map_zero, h0])
      rcases ValuationRing.isInteger_or_isInteger O T with ⟨t, ht⟩ | ⟨s, hs⟩
      · exact hne t ht
      · have hsm : s ∈ IsLocalRing.maximalIdeal O := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          intro hu
          obtain ⟨u, rfl⟩ := hu
          apply hne (↑u⁻¹)
          rw [map_units_inv, hs, inv_inv]
        obtain ⟨r, hr, -⟩ := sqrtO O K Δ h (1 - 4 * s ^ 2) 1 isUnit_one (by
          have e' : (1 - 4 * s ^ 2) - 1 ^ 2 = s * (-(4 * s)) := by ring
          rw [e']
          exact Ideal.mul_mem_right _ _ hsm)
        have hTS : T * algebraMap O K s = 1 := by
          rw [hs]
          exact mul_inv_cancel₀ hT0
        have hR : (algebraMap O K r) ^ 2 = 1 - 4 * (algebraMap O K s) ^ 2 := by
          rw [← map_pow, hr, map_sub, map_one, map_mul, map_pow, map_ofNat]
        apply nz (-τ * e.im - T * algebraMap O K r) (2 * e.im) (mul_ne_zero h2K hq)
        linear_combination T ^ 2 * hR - 4 * (T * algebraMap O K s + 1) * hTS + 4 * hN +
          (T + 2 * e.re + τ * e.im) * hTd
    exact isIntegral_of_trace_norm t 1 ht.symm (by rw [hn, map_one])

private theorem norm_quo {K : Type} [Field K] {τ : K} (z : (Etau K τ)ˣ) : QuadraticAlgebra.norm (quo z) = 1 := by
  simp only [quo, map_mul, QuadraticAlgebra.norm_star]
  rw [← map_mul, Units.mul_inv, map_one]

theorem UpperTheory.compactTorusUnits_eq_top_of_nonsplit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ¬ IsSquare (τ ^ 2 - 4) → Cint O τ = ⊤ := by
  intro O K _ _ _ _ _ Δ τ h _ hτ
  rw [eq_top_iff]
  intro z _
  exact ⟨int_of_norm_one h hτ _ (norm_quo z), int_of_norm_one h hτ _ (norm_quo z⁻¹)⟩
